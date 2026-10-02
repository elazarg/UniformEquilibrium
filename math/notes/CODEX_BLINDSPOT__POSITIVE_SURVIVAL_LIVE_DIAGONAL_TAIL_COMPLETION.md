# Positive-survival Zeno completion is diagonal-carrier data

Author: `CODEX_BLINDSPOT`

## Status

Active mathematical audit, 2026-09-03.  Two terminal-splice criteria are
proved below in ordinary mathematics.  The first is already present in a
stronger checked source-native form in the project.  The second isolates the
smallest survival-weighted tail fields needed by a growing finite exact-prefix
compiler.  Neither is a new arbitrary-game producer.

The main redirect is exact:

> A genuinely positive **joint**-survival Zeno limit is not the live branch
> currently called `positiveHost`.  Positive joint reach transports global
> approximate Nash play to the actual suffix after division by reach, and
> compactification makes that suffix limit diagonal.  This case is already
> checked and already yields a uniform-equilibrium payoff.
>
> The current `positiveHost` branch has joint survival tending to zero and
> only one player-deleted survival bounded below.  It is a live **cap**
> boundary, not a live on-path tail.  Its packet retains no global Nash bound,
> no exact-Nash condition on the arbitrary premark word, and only one local
> marked-host defect equality.  Those fields do not instantiate a terminal
> splice.

An exact Fin4 regression in Section 7 shows that the positive-host clock
pattern, an actual diagonal postmark tail, positive host-cleared marked mass,
and zero marked-host defect can coexist with unit outsider exploitability.

No Lean files, exports, or shared indexes were edited.

## 1. Self-contained question

Fix a finite nonempty player set `I` and a quitting reward table `r`, with
`|r_k(S)| <= M`.  For every rank `n`, let

\[
 W_n=(x_{n,0},\ldots,x_{n,L_n-1})
\]

be a finite literal product-root word and let `tau_n` be an actual behavioral
tail.  Write

\[
 \sigma_n=W_n\star\tau_n,
 \qquad
 \alpha_n=\Pr(W_n\hbox{ jointly survives}),
 \qquad
 \beta_{n,k}=\Pr(W_n\hbox{ survives after deleting }k).
\]

All deviations below are unrestricted behavioral deviations, including
Never and arbitrarily late stopping.  The question is:

> What finite-dimensional tagged data suffice to make either the actual
> tails `tau_n`, or the full splices `sigma_n`, terminal approximate Nash
> profiles with one convergent payoff target when `L_n -> infinity` and a
> survival clock remains live?

There are two logically different answers: extraction from already Nash full
profiles, and compilation from an independently supplied semantic tail.

## 2. Minimal positive-joint extraction theorem

### Theorem 2.1

Assume:

1. `sigma_n=W_n star tau_n` is an actual literal decomposition;
2. `sigma_n` is terminal `epsilon_n`-Nash against every behavioral deviation;
3. `alpha_n>0` and

   \[
                    \epsilon_n/\alpha_n\longrightarrow0.       \tag{2.1}
   \]

Then `tau_n` is terminal `(epsilon_n/alpha_n)`-Nash against every behavioral
deviation.  Consequently some subsequence of its terminal semantic pairs
converges to a diagonal carrier point `(y,y)`, the tail payoffs converge to
`y` on that subsequence, and `y` is a uniform-equilibrium payoff.

In particular, if `alpha_n -> alpha_infty>0` and `epsilon_n -> 0`, (2.1) is
automatic.

### Proof

Fix player `k` and any complete tail deviation `d`.  In the full profile,
let `k` copy its prescribed marginal at every row of `W_n` and switch to `d`
exactly when the suffix is reached.  The exact common-prefix identity gives

\[
 U_k(\sigma_n[k\leftarrow\operatorname{copy}(W_n,d)])
      -U_k(\sigma_n)
   =\alpha_n\bigl(U_k(\tau_n[k\leftarrow d])-U_k(\tau_n)\bigr). \tag{2.2}
\]

The left side is at most `epsilon_n`.  Division by positive `alpha_n` proves
the tail Nash bound uniformly over all `d`.

The terminal semantic pairs

\[
 P_n=(U(\tau_n),B(\tau_n))
\]

belong to the compact terminal-semantic carrier.  Pass to a convergent
subsequence `P_{n_j}->P`.  The preceding Nash bound and (2.1) give
`P.2_k-P.1_k<=0` for every `k`.  Carrier membership gives the reverse
nonnegativity, so `P=(y,y)` for `y=P.1`.  The actual tails on this same
subsequence have payoff converging to `y` and exploitability tending to zero.
Fixed-target terminal acceptance, equivalently the diagonal-carrier theorem,
makes `y` a uniform-equilibrium payoff.  `□`

### Minimality of the quantitative tag

Positive limiting reach is convenient but stronger than necessary.  The
exact transmitted deviation error is the ratio (2.1).  No Bellman targets,
root-by-root Nash witnesses, stationary structure, or Zeno ordinal are needed
for Theorem 2.1.  Conversely, when `alpha_n` vanishes, global error
`epsilon_n` alone gives no suffix Nash information unless its decay is faster
than `alpha_n`.

## 3. Survival-weighted diagonal splice theorem

The reverse direction starts with an actual tail and asks whether a growing
finite prefix produces full approximate Nash profiles.

Let `Phi_W` denote the exact finite composition of terminal-semantic prefix
maps along a literal word `W`.  For a declared tail vector `y_n`, put

\[
 Q_n=\Phi_{W_n}(y_n,y_n),\qquad
 z_n=Q_n.1,\qquad
 \delta_{n,k}=Q_n.2_k-Q_n.1_k.                         \tag{3.1}
\]

Here `Q_n` is an algebraic reference pair.  It need not be asserted
executable.  Write the actual tail pair as

\[
 P_n=(u_n,b_n).
\]

### Theorem 3.1

Assume, for every player `k`,

\[
 z_n\longrightarrow z,\qquad
 \delta_{n,k}\longrightarrow0,                        \tag{3.2}
\]

and the two transmitted tail seams vanish:

\[
 \alpha_n|u_{n,k}-y_{n,k}|\longrightarrow0,            \tag{3.3}
\]

\[
 \beta_{n,k}(b_{n,k}-y_{n,k})_+\longrightarrow0.       \tag{3.4}
\]

Then the literal full profiles `sigma_n=W_n star tau_n` have prescribed
payoffs converging to `z` and terminal exploitability tending to zero.
Hence `z` is a uniform-equilibrium payoff.

### Proof

Changing only the suffix behind `W_n` changes prescribed payoff coordinate
`k` by exactly joint survival times the suffix payoff change.  Thus

\[
 |U_k(\sigma_n)-z_{n,k}|
    =\alpha_n|u_{n,k}-y_{n,k}|.                        \tag{3.5}
\]

For the envelope coordinate, one root acts by the maximum of a Quit endpoint,
which is independent of the tail cap, and a Continue endpoint, in which
`b_k` has coefficient equal to opponent survival.  Monotonicity and the
one-sided Lipschitz inequality for `max`, iterated over the word, give

\[
 B_k(\sigma_n)-Q_n.2_k
   \le \beta_{n,k}(b_{n,k}-y_{n,k})_+.                 \tag{3.6}

Subtract (3.5) from (3.6):

\[
 B_k(\sigma_n)-U_k(\sigma_n)
 \le \delta_{n,k}
    +\beta_{n,k}(b_{n,k}-y_{n,k})_+
    +\alpha_n|u_{n,k}-y_{n,k}|.                        \tag{3.7}

Equations (3.2)--(3.4) prove vanishing unrestricted behavioral debt, while
(3.2)--(3.3) prove payoff convergence.  Terminal acceptance gives the
claim.  `□`

### Exact-Nash specialization

If each `W_n` carries declared vectors

\[
 v_{n,0},\ldots,v_{n,L_n}=y_n
\]

such that `v_{n,t}=F_r(x_{n,t},v_{n,t+1})` and every root is exact Nash at
its retained successor, exact diagonal prefixing gives

\[
 Q_n=(v_{n,0},v_{n,0}),
\]

so every `delta_{n,k}` is exactly zero.  Finite singleton-flow meshes can be
included by retaining their nonzero ideal prefix debt in the `delta` tag;
the finite jump--flow estimates in the frozen companion note give sufficient
mesh bounds.  This avoids pretending that a limiting flow arc is itself a
literal date.

## 4. What positive joint survival forces

Suppose `alpha_n>=a>0`.  Since `beta_{n,k}>=alpha_n`, (3.3) forces

\[
 u_n-y_n\longrightarrow0.
\]

Actual terminal semantics have `b_n>=u_n`.  Condition (3.4) then forces

\[
 b_n-y_n\longrightarrow0.
\]

Thus at a genuinely positive-joint live limit, the survival-weighted splice
conditions are not weaker than an actual diagonal tail: after a compact
subsequence `y_n->y`, the actual tail semantic pairs converge to `(y,y)`.
The live tail is itself a uniform-equilibrium payoff by the checked diagonal-
carrier characterization.

This is the precise no-free-lunch boundary.  Compact payoff/root witness
syntax cannot manufacture positive-joint completion.  A sufficient live-tail
field either explicitly supplies diagonal carrier membership or contains
equivalent source data, such as positive reach plus vanishing full-profile
Nash error from Theorem 2.1.

## 5. Checked project theorem already covering genuine positive joint reach

The preceding conclusion is not a missing Fin4 lemma.

`QuittingPositiveJointPrefixReachSource.punishment_nash_of_joint_pos` in
`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointPrefixReachEndpoint.lean`
is the checked division-by-reach step.  Its error is exactly twice the source
error divided by prefix joint survival.

The same file proves:

- `punishmentNashError_tendsto_zero`;
- `exists_punishmentEndpoint`, which compactifies the actual reached tails;
- `QuittingPositiveJointPrefixReachPunishmentEndpoint.debt_eq_zero` and
  `payoff_eq_envelope`; and
- `exists_realizers`, retaining actual behavioral realizers.

`QuittingPositiveJointPrefixReachPunishmentEndpoint.isUniformEquilibriumPayoff`
in `PositiveJointEndpointUniformPayoff.lean` consumes that diagonal carrier
point directly.  Independently,
`isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier` in
`UniformPayoffTerminalSemanticCarrier.lean` states the exact general
equivalence.

Finally, `PositiveJointExactPrefixOrbitDiagonal.lean` proves that every exact
semantic-prefix orbit launched from this reached endpoint remains diagonal,
and that a summable all-Continue port limit remains a diagonal carrier point.
Therefore reopening “positive joint Zeno completion” as a new producer route
would duplicate checked work.  The missing interface is at zero joint reach
with a surviving deleted cap clock.

## 6. Audit of the current Zeno source and clock packets

### 6.1 Actual zero-mass Zeno source

`FinFourActualZenoDeletedSurvivalSource` in
`Research/Quitting/FinFourProducerAtlas/ActualZenoDeletedSurvivalSource.lean`
does retain useful literal data:

- the actual target and comparison profiles;
- the arbitrary `newWord` and complete `combinedWord`;
- whole and postmark-tail semantic/law convergence; and
- the complete postmark reference behavioral spine.

But it also proves

\[
 \alpha_n=Pr(\text{combinedWord survives jointly})\longrightarrow0.
\]

The new prefix word is arbitrary: `rawDecoration` deliberately allows every
finite product-root word with no Nash condition.  No field makes the actual
whole profiles `epsilon_n`-Nash, no field bounds the ideal debts
`delta_{n,k}` of (3.1), and no field gives the ratio
`epsilon_n/alpha_n -> 0`.  Hence neither Theorem 2.1 nor Theorem 3.1 applies.

There is a stronger exact failure of diagonality.  The checked declaration
`FinFourNormalizedInertVanishingDensityBoundary.limit_tailDebt_eq_minimum`
identifies the limiting postmark tail-debt sum with the retained minimum
debt.  In the contrary no-uniform-payoff chamber this minimum is strictly
positive.  Thus the tail limit supplied by this packet is explicitly
off-diagonal, not a missing diagonal tail waiting to be unpacked.

### 6.2 Positive host is deleted-clock live, not joint live

`FinFourActualZenoPositiveHost` in
`ActualZenoHostCompression.lean` gives one host `h` and `eta>0` with

\[
 \beta_{n,h}\ge\eta,
 \qquad \beta_{n,k}\to0\ (k\ne h),
 \qquad \alpha_n\to0.                                 \tag{6.1}
\]

The last equality comes from the underlying actual-Zeno source and survives
the selected subsequence.  Thus this is not the hypothesis of Theorem 2.1.
It does not reach the actual tail with positive on-path probability.

The `FixedEndpoint` refinement adds positive host-cleared marked mass, exact
zero defect for the host at the marked row, unchanged nonhost behavior, and
the complete postmark reference tail.  It does **not** add:

1. exact or approximate Nash control for the arbitrary premark word;
2. zero marked-root defects for nonhosts;
3. a bound `delta_{n,k}->0` for the complete host-cleared prefix; or
4. the surviving host-cap seam

   \[
   \beta_{n,h}(b_{n,h}-y_{n,h})_+\longrightarrow0.      \tag{6.2}
   \]

Because `beta_{n,h}` stays positive, (6.2) is the one tail coordinate that
cannot be erased by the clock.  Positive marked mass and one local root
defect do not imply it.

### 6.3 Fully screened finite clearing

In the fully screened arm every `beta_{n,k}` vanishes, so bounded suffix-cap
differences are erased.  `FullyScreenedClearingFamily` then produces
source-attached concentrated packets and a fixed finite mechanism label.
This is a structural clearing result, not a terminal Nash result.  Its
`consumerResult` ends in the strategic-singleton or collision-minimum
residuals; it supplies neither a whole-profile Nash error tending to zero nor
an ideal prefix debt `delta_n` tending to zero.  Full screening solves the
tail term (3.4), not the prefix term (3.2).

### 6.4 Scalar Zeno clock

`Research/Quitting/NormalizedPassportZenoBoundary.lean` retains scalar
prefix/defect ledgers only.  It is explicitly not a quitting game and has no
behavior profile, terminal semantic pair, or complete unilateral-deviation
cap.  It cannot instantiate any actual-profile field of either theorem.

## 7. Exact Fin4 regression against the positive-host field list

Let players be `0,1,2,3`, with host `0`.  Define every reward coordinate to
be zero except

\[
                    r_1(\{1,2\})=1.                   \tag{7.1}
\]

Use one original premark root at which player `0` Quits surely and players
`1,2,3` Continue surely.  Then

\[
 \alpha=0,\qquad \beta_0=1,\qquad
 \beta_1=\beta_2=\beta_3=0.                            \tag{7.2}
\]

For the host-cleared endpoint, force player `0` to Continue through that
premark row.  At the marked row let player `2` Quit surely and every other
player Continue.  Follow this by the all-Continue tail.

All advertised local boundary facts hold exactly:

- the original word has the positive-host clock pattern (7.2);
- the host-cleared profile reaches marked coalition `{2}` with mass `1`;
- changing the host's marked action gives it payoff `0` either way, so its
  marked coordinate Nash defect is `0`;
- nonhost behavior is unchanged by the host endpoint selection; and
- the postmark tail is actual and has diagonal semantic pair `(0,0)`, since
  all singleton rewards and the Never payoff are zero.

Nevertheless player `1` gains exactly `1` by Quitting at the marked row.
The prescribed marked outcome `{2}` pays it `0`, while its deviation produces
`{1,2}` and pays it `1`.  The host-cleared endpoint profile therefore has
terminal exploitability `1`.

This is not claimed to realize every provenance field of the current Fin4
producer.  It is an exact implication counterexample: the named clock,
marked-mass, postmark-tail, unchanged-opponent, and one-coordinate defect
fields alone do not imply the missing terminal consumer.  At least complete
prefix debt control, or an additional paid exit generated from its failure,
is mathematically necessary.

## 8. Proved facts, checked facts, and proposals

### Proved here in ordinary mathematics

- The ratio criterion of Theorem 2.1, including unrestricted behavioral
  deviations and compact diagonal-tail extraction.
- The survival-weighted semantic splice bound (3.7) and Theorem 3.1.
- Positive joint survival forces an actual diagonal tail under the splice
  hypotheses.
- The exact Fin4 regression in Section 7.

### Already checked in Lean

- Exact copied-prefix payoff transport in
  `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`.
- Common-prefix unrestricted-cap contraction in
  `UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`.
- Compact terminal-semantic carrier realization and prefixing in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- The complete positive-joint extraction and diagonal endpoint consumer
  listed in Section 5.
- The current actual-Zeno and positive-host packet fields listed in Section
  6.

### Not proved

- The current positive-host or fully screened packet outputs satisfy
  `delta_n->0`.
- The positive host satisfies the cap seam (6.2).
- A failure of (6.2) regenerates a source or feeds an existing paid-port
  consumer.
- Arbitrary finite quitting games supply a self-generating jump--flow
  execution certificate.

## 9. Concrete next question

Do not seek a full diagonal postmark tail in the positive-host branch; joint
survival has already erased prescribed tail payoff and every nonhost tail cap.
The smallest live question is one-coordinate and disjunctive:

> Along the fixed positive-host endpoint, prove either the host-cap seam
> (6.2) together with vanishing complete prefix ideal debt, or extract from
> their failure one source-attached paid deviation with a fixed player and a
> quantitative reach floor that enters an existing paid-port/collision
> consumer.

The regression shows why checking only the marked host is insufficient:
nonhost prefix defects must either vanish or be explicitly consumed.  This
is the exact place where the present source/clock route lacks executable
information.

## 10. Sources inspected

- `math/SOURCES.md`, `math/GOAL.md`, `math/questions/README.md`, and
  `math/questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`.
- `docs/FRONTIER.md` and `docs/TOOLKIT.md`, restricted to the normalized
  passport, actual-Zeno, clock-clearing, and terminal-semantic entries.
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`.
- `UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`.
- `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
- `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointPrefixReachEndpoint.lean`.
- `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointEndpointUniformPayoff.lean`.
- `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointExactPrefixOrbitDiagonal.lean`.
- `Research/Quitting/NormalizedPassportZenoBoundary.lean`.
- `Research/Quitting/FinFourProducerAtlas/NormalizedInertVanishingDensityBoundary.lean`.
- `Research/Quitting/FinFourProducerAtlas/ActualZenoDeletedSurvivalSource.lean`.
- `Research/Quitting/FinFourProducerAtlas/ActualZenoHostCompression.lean`.
- `Research/Quitting/FinFourProducerAtlas/FullyScreenedFiniteClockClearing.lean`.
- `Research/Quitting/FinFourProducerAtlas/ActualZenoFullyScreenedSiblingCoalescence.lean`.
