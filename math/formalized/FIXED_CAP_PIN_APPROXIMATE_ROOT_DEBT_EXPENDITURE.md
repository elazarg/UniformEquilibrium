# Fixed cap pins force approximate-root debt expenditure

Authors: CODEX_HAHN

Independent reviews of the two core notes:
[CODEX_SPINOZA, exact theorem](../feedback/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP__BY_CODEX_SPINOZA.md),
[CODEX_NEGATIVE_CERTIFICATE, exact theorem](../feedback/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP__BY_CODEX_NEGATIVE_CERTIFICATE.md),
[CODEX_SPINOZA, approximate theorem](../feedback/CODEX_HAHN__APPROXIMATE_CAP_PIN_DEBT_DROP_AND_VISIT_BUDGET__BY_CODEX_SPINOZA.md), and
[CODEX_NEGATIVE_CERTIFICATE, approximate theorem](../feedback/CODEX_HAHN__APPROXIMATE_CAP_PIN_DEBT_DROP_AND_VISIT_BUDGET__BY_CODEX_NEGATIVE_CERTIFICATE.md).

## Exact statement

Let `I` be a finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a bounded quitting reward table. Never pays zero. For a terminal semantic
pair

\[
 X=(u,B),
\]

`u` is the prescribed terminal payoff and `B` is the vector of suprema over
all unilateral behavioral deviations, including randomized and arbitrarily
late stopping times and literal Never. Write

\[
 d_i(X)=B_i-u_i.
\]

Fix a player `b`, constants \(M,\gamma>0\), and put

\[
 s_b=r_b(\{b\}).
\]

Assume

\[
 |r_i(S)|\le M,\qquad |u_i|\le M                              \tag{1}
\]

for every player and every nonempty terminal coalition, and

\[
 d_b(X)\ge\gamma,
 \qquad |B_b-s_b|\le\frac{\gamma}{4}.                         \tag{2}
\]

Define

\[
 \delta_b=min\left\{\frac{\gamma}{2},
                     \frac{\gamma^2}{16M}\right\}>0.          \tag{3}
\]

Let `q` be any independent product root which is
\(\varepsilon\)-Nash in the one-stage quitting game whose all-Continue payoff
is the literal vector `u`, where \(\varepsilon\ge0\). Prefix `q` to the pair
`X`, using `B` as the complete cap after the all-Continue outcome. Then

\[
 \boxed{
 d_b(X)-d_b(\operatorname{Prefix}(q,X))
 \ge\delta_b-\varepsilon.}                                   \tag{4}
\]

For an exact root, the named coordinate therefore drops by at least
\(\delta_b\). If all input coordinate debts are nonnegative, every other
coordinate is nonincreasing under an exact root, so total terminal-semantic
debt also drops by at least \(\delta_b\).

The theorem is dimension-independent and pointwise. It assumes neither a
positive global debt minimum nor an absorption floor for exact roots.

### Vertical finite-visit consequence

Let \(X_0,X_1,\ldots\) be actual terminal semantic pairs with

\[
 X_{k+1}=\operatorname{Prefix}(q_k,X_k),                       \tag{5}
\]

where `q_k` is \(\varepsilon_k\)-Nash against the prescribed payoff of
`X_k`. Let `V` be the set of indices at which (2) holds for the same fixed
player `b` and the same \(\gamma\). If

\[
 E=\sum_k\varepsilon_k<\infty,                                \tag{6}
\]

then

\[
 |V|\le
 \left\lfloor\frac{2M+E}{\delta_b}\right\rfloor.             \tag{7}
\]

In particular, an exact vertical prefix chain visits the fixed cap-pin
chamber at most \(\lfloor2M/\delta_b\rfloor\) times.

### Arbitrary re-entry replenishment ledger

The preceding conclusion has an exact extension which exposes the remaining
source-reconstruction obstruction. Let \(S_k\) be actual source semantic
pairs. For each `k`, let `q_k` be \(\varepsilon_k\)-Nash against the
prescribed payoff of `S_k`, and put

\[
 P_k=\operatorname{Prefix}(q_k,S_k).                           \tag{8}
\]

Between `P_k` and the next source `S_{k+1}`, permit an arbitrary re-entry
operation: a behavioral response, a same-law reset, a causal re-realization,
or any other source reconstruction. Define the positive replenishment of the
named debt coordinate by

\[
 \kappa_k=
 \left[d_b(S_{k+1})-d_b(P_k)\right]_+.                        \tag{9}
\]

Let `V` be the set of `k` for which `S_k` satisfies (2). For every finite
`N`,

\[
 \boxed{
 |V\cap\{0,\ldots,N-1\}|\,\delta_b
 \le d_b(S_0)+\sum_{k<N}(\varepsilon_k+\kappa_k).}            \tag{10}
\]

If `S_0` is actual under the reward bound, then \(d_b(S_0)\le2M\). Hence
finite total root error and finite total re-entry replenishment imply only
finitely many returns to the same cap-pin chamber.

There is also a direct semantic-seam form. Define

\[
 \eta_k=
 |S_{k+1}.1_b-P_k.1_b|
 +|S_{k+1}.2_b-P_k.2_b|.                                     \tag{11}
\]

Then

\[
 \kappa_k\le\eta_k.                                         \tag{12}
\]

Consequently, if

\[
 \sum_k\varepsilon_k<\infty,
 \qquad
 \sum_k\eta_k<\infty,                                      \tag{13}
\]

the fixed cap-pin chamber can occur only finitely often. Conversely, every
infinite source-reconstructed recurrence of that chamber must pay either
infinite total root-Nash error or a nonsummable semantic seam in the named
debt coordinate.

## Conjecture-facing change

The live quantitative paid-port obligation asks how a source-attached paid
row can be converted into a charged Nash--Bellman return, a renewable finite
rank, or a contradiction to positive minimum debt. The structured tropical
source supplies more local data: one fixed paid player has a complete cap
converging to its singleton reward while its debt stays uniformly positive.

The theorem consumes every one-stage exactification of that source. Every
exact payoff-tail root spends one fixed amount of the **same named complete
behavioral debt coordinate**, regardless of its support, collision pattern,
or absorption probability. Thus a mixed absorbing exact root is not a new
local residue, and the cap-pinned chamber cannot be a recurrent component of
the vertical exact-prefix relation.

The re-entry ledger identifies the exact remaining global cost. Any
horizontal or source-reconstruction operation which returns infinitely often
to this chamber must replenish the spent coordinate by a nonsummable amount.
The unresolved task is to consume that replenishment as chronological charge
or prove that the actual Fin4 source construction cannot sustain it. The
present result does not perform that final conversion.

## Definitions and assumptions

For a product root `q`, let

\[
 q_b=\Pr_q(b\text{ Quits}),
 \qquad
 s=\prod_{j\ne b}(1-q_j),
 \qquad
 \alpha=1-s.                                                  \tag{14}
\]

Thus `s` is the probability that every opponent of `b` Continues and
\(\alpha\) is the probability that at least one opponent Quits.

Let

\[
 Q=Q_b(q_{-b}),
 \qquad
 C=C_b(q_{-b};u_b),
 \qquad
 e=Q-C.                                                       \tag{15}
\]

Here `Q` is `b`'s payoff after forcing Quit in the current row. The value `C`
is its payoff after forcing Continue, using `u_b` only when all opponents
Continue. The ordinary product root is \(\varepsilon\)-Nash when no pure
current-action deviation improves the prescribed endpoint mixture by more
than \(\varepsilon\). Since there are two actions, this is equivalent to
Nash against every mixed current-action deviation.

The semantic prefix cap uses the full old-tail value `B_b`, not a stationary
or finite-clock approximation. Thus the output debt in (4) includes every
unilateral behavioral deviation in the attached tail.

For a pair-valued seam, the coordinate metric in (11) is the sum of the
absolute prescribed-payoff and cap changes. If instead the pair is equipped
with the maximum norm over both vectors, then

\[
 \eta_k\le2\|S_{k+1}-P_k\|_\infty.                            \tag{16}
\]

No claim is made for a private correlated recommendation. The current root
is an ordinary independent mixed-strategy profile. The scalar proof also
works for an exogenous opponents' coalition law independent of `b`'s action,
but additional private information would change the deviation class.

## Proof

### The arbitrary-root prefix identity

Put \(d=d_b(X)=B_b-u_b\). The prescribed payoff of `b` at the new root is

\[
 u'_b=q_bQ+(1-q_b)C=C+q_be.                                  \tag{17}
\]

If `b` Continues at the new root and then uses its complete old-tail cap,
replacing `u_b` by \(B_b=u_b+d\) changes the Continue endpoint by exactly
`sd`. Hence

\[
 B'_b=\max\{Q,C+sd\}=C+\max\{e,sd\}.                        \tag{18}
\]

Subtracting (17) from (18) gives

\[
 \boxed{d'_b=\max\{e,sd\}-q_be.}                            \tag{19}
\]

This identity uses no Nash hypothesis.

### Approximate root inequalities

If \(e\ge0\), changing `b`'s mixture to pure Quit gains
\((1-q_b)e\). If \(e\le0\), changing it to pure Continue gains
\(q_b(-e)\). Therefore \(\varepsilon\)-Nash gives

\[
 e\ge0\Longrightarrow(1-q_b)e\le\varepsilon,
 \qquad
 e\le0\Longrightarrow q_b(-e)\le\varepsilon.                \tag{20}
\]

Equations (19)--(20) imply

\[
 d'_b\le sd+\varepsilon.                                     \tag{21}
\]

Indeed, if \(e\ge sd\), then \(e\ge0\) and
\(d'_b=(1-q_b)e\le\varepsilon\). If \(0\le e<sd\), then
\(d'_b=sd-q_be\le sd\). If \(e<0\), then
\(d'_b=sd+q_b(-e)\le sd+\varepsilon\).

In particular, since \(s\le1\) and \(d\ge0\),

\[
 d'_b-d\le\varepsilon.                                      \tag{22}
\]

### The cap-pin case split

For an opponents' quitting coalition \(T\subseteq I\setminus\{b\}\), define

\[
 f(T)=
 \begin{cases}
 s_b-u_b,&T=\varnothing,\\
 r_b(T\cup\{b\})-r_b(T),&T\ne\varnothing.
 \end{cases}                                                  \tag{23}
\]

If \(\pi_q\) is the opponents' product law, then

\[
 e=\sum_T\pi_q(T)f(T).                                       \tag{24}
\]

The pin and debt floor give

\[
 s_b-u_b=(s_b-B_b)+d\ge\frac{3\gamma}{4}.                    \tag{25}
\]

Every value in (23) has magnitude at most \(2M\). The nonempty opponent
coalitions have total mass \(\alpha\), so

\[
 |e-(s_b-u_b)|
 =\left|\sum_{T\ne\varnothing}\pi_q(T)
          (f(T)-f(\varnothing))\right|
 \le4M\alpha.                                                \tag{26}
\]

If \(\alpha\ge\gamma/(16M)\), equation (21) gives

\[
 d-d'_b\ge\alpha d-\varepsilon
 \ge\frac{\gamma^2}{16M}-\varepsilon.                       \tag{27}
\]

If \(\alpha<\gamma/(16M)\), equations (25)--(26) give

\[
 e>\frac{\gamma}{2}.                                        \tag{28}
\]

When \(e\ge sd\), equations (19)--(20) give

\[
 d'_b=(1-q_b)e\le\varepsilon,
 \qquad d-d'_b\ge\gamma-\varepsilon.                       \tag{29}
\]

When \(e<sd\),

\[
\begin{aligned}
 d-d'_b
 &=d-(sd-q_be)\\
 &=(1-s)d+q_be\\
 &\ge q_be\\
 &=e-(1-q_b)e\\
 &\ge\frac{\gamma}{2}-\varepsilon.
\end{aligned}                                                 \tag{30}
\]

Equations (27), (29), and (30) prove (4). For an exact root,
\(\varepsilon=0\). The checked exact positive-part debt action also shows
that every other nonnegative debt coordinate is nonincreasing, proving the
total-debt statement.

### Vertical visit budget

At `k` in `V`, equation (4) gives

\[
 d_b(X_{k+1})
 \le d_b(X_k)-\delta_b+\varepsilon_k.                         \tag{31}
\]

At every other `k`, equation (22) gives

\[
 d_b(X_{k+1})\le d_b(X_k)+\varepsilon_k.                     \tag{32}
\]

Telescope (31)--(32) through `N` edges:

\[
 d_b(X_N)
 \le d_b(X_0)
 -|V\cap\{0,\ldots,N-1\}|\delta_b
 +\sum_{k<N}\varepsilon_k.                                  \tag{33}
\]

Actual semantic debt is nonnegative and the reward bound gives
\(d_b(X_0)\le2M\). Rearrangement proves (7), first on every finite prefix and
then on the whole chain.

### Re-entry replenishment

By definition of positive part,

\[
 d_b(S_{k+1})\le d_b(P_k)+\kappa_k.                           \tag{34}
\]

Apply (4) when `k` is in `V`, apply (22) otherwise, and then use (34). This
gives

\[
 d_b(S_{k+1})
 \le d_b(S_k)
 -\mathbf 1_{\{k\in V\}}\delta_b
 +\varepsilon_k+\kappa_k.                                   \tag{35}
\]

Telescoping (35) and using nonnegativity of the final debt proves (10).

For the seam estimate, expand the debt difference:

\[
 d_b(S_{k+1})-d_b(P_k)
 =\bigl(S_{k+1}.2_b-P_k.2_b\bigr)
  -\bigl(S_{k+1}.1_b-P_k.1_b\bigr).
\tag{36}
\]

The positive part of the left side is bounded by the sum of the absolute
values on the right, proving (12). Equations (10)--(13) follow.

## Source correspondence

The [exact pointwise theorem and tropical adapter](../notes/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP.md)
were independently reviewed at frozen note SHA-256
`a4b9e7cf7b60a2566c07eeb47a942549a5bd68715c42d8a197d1c84705198a75`.
The [approximate identity and vertical visit theorem](../notes/CODEX_HAHN__APPROXIMATE_CAP_PIN_DEBT_DROP_AND_VISIT_BUDGET.md)
were independently reviewed at frozen note SHA-256
`5f84a9449b29cd50abc8ee0b39d4163210f340377a330613e6701324f208d941`.
The interleaved re-entry ledger (8)--(13) is new in this packet and must be
reviewed at this packet's frozen hash before promotion.

The actual source is the frozen reviewed export
[FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md](FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md),
SHA-256
`52c87dac80db59733cf4f3bbdb26bcdf9a915060d94a94acc5bc29df5a51a027`.
It supplies actual stationary last-edge sources \(\tau_n\), a fixed final
mover `b`, and \(\gamma>0\) such that literal Quit at date zero attains `b`'s
complete behavioral cap with gain at least \(\gamma\). Thus

\[
 d_b(\operatorname{Sem}(\tau_n))\ge\gamma.                    \tag{37}
\]

Every semantic cluster of the source sequence has `b`-cap equal to \(s_b\).
Compactness turns this cluster identity into

\[
 B_b(\operatorname{Sem}(\tau_n))\longrightarrow s_b.          \tag{38}
\]

Otherwise a subsequence staying a fixed distance from \(s_b\) would have a
cluster point violating the identity. Equations (37)--(38) instantiate the
static theorem for every sufficiently late exact root, and instantiate the
approximate theorem once the root errors are small.

The tropical source is produced under the no-uniform-payoff branch and has
substantial additional Fin4 ancestry and off-minimum data. None of those
extra fields is used by this theorem. In particular, source hazard decay and
positive global minimum debt are not hidden assumptions in the adapter.

The following checked declarations contain the exact semantic components:

- `quittingTerminalSemanticPrefix`,
  `quittingTerminalSemanticDebt_prefix_eq_blockAct`, and
  `quittingTerminalSemanticDebt_prefix_le` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingRootSuccessorPayoff_eq_endpointMix` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`; and
- `isεQuittingRootNash_iff_coordinateNashDefect_le` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`.

The new mathematical content is the arbitrary-root debt identity (19), the
opponent-law case split, its approximate-root form, and the vertical and
interleaved telescopes. No external literature theorem is used.

## Boundary tests

1. **No cap pin.** Take two players `b,k`. Let the prescribed profile make
   `k` Quit surely while `b` Continues, and set

   \[
   r_b(\{b\})=0,
   \quad r_b(\{k\})=1,
   \quad r_b(\{b,k\})=2.
   \]

   Then \(u_b=1\), \(B_b=2\), and `b` has debt one. Choose `k`'s rewards so
   its prescribed payoff and singleton reward are both one. The all-Continue
   root is exact against `u` and its prefix is the identity, so the positive
   debt is not spent. A fixed debt without the cap pin is insufficient.

2. **No fixed debt floor.** Modify the preceding values so
   \(s_b=u_b=1\) and \(B_b=1+\gamma_n\) with
   \(\gamma_n\downarrow0\). The cap approaches the singleton reward, but the
   debt scale and every forced expenditure can vanish.

3. **Approximate error is not summable.** Equation (22) permits each
   nonchamber approximate prefix to replenish up to its Nash error. The
   condition \(\varepsilon_k\to0\) alone does not imply a finite visit count.

4. **Horizontal reset.** A complete strategy response by another player can
   change `b`'s unrestricted cap and prescribed payoff at first order. Such an
   operation is measured by \(\kappa_k\) or \(\eta_k\); it is not silently
   classified as an exact prefix. If these re-entry costs are nonsummable,
   the ledger gives no contradiction.

5. **No renewal from a fixed drop.** The cap after one prefix is

   \[
   \max\{Q_b(q_{-b}),C_b(q_{-b};B_b)\},
   \]

   which need not remain close to \(s_b\). Neither the static theorem nor the
   tropical source export supplies the cap pin at the child.

6. **Behavioral scope.** Approximate root Nash controls the current Boolean
   action only. The semantic prefix cap nevertheless includes the unrestricted
   old-tail response class. The theorem does not claim that the non-Nash tail
   becomes a terminal Nash continuation.

7. **Correlation.** Ordinary Nash mixed actions are independent. A private
   correlated recommendation may reveal information and change the available
   deviations; it is outside the theorem.

## Adapter and consumer

The actual-data adapter is (37)--(38): a fixed exact-cap Quit0 gain supplies
the debt floor, and the source's cluster cap identity supplies the eventual
absolute pin. Given any exact payoff-tail root provided by finite mixed Nash
existence, literal semantic prefixing produces an actual carrier child and
spends at least \(\delta_b\) of the named complete behavioral debt.

This strictly consumes the one-stage exact-root-support ambiguity at the
structured tropical port. The output is a quantitative lower-debt child with
literal predecessor/successor semantics. It is not yet a terminal consumer
for
[FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md](../questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md):
the child need not be another
tropical stationary source, and arbitrary source reconstruction can pay the
nonsummable replenishment allowed by (10).

The vertical visit bound is the downstream finite-rank consumer only for
literal approximate-prefix chains with finite total error. The interleaved
ledger converts any proposed broader renewal into one precise new obligation:
control the positive named-coordinate replenishment, or prove that its
nonsummable accumulation creates chronological charge.

## Lean handoff

The narrow implementation order is:

1. prove the arbitrary-root coordinate identity (19) directly from
   `quittingTerminalSemanticPrefix`,
   `quittingRootSuccessorPayoff_eq_endpointMix`, and the Continue-payoff
   update identity;
2. extract the two scalar inequalities (20) from the coordinate root Nash
   defect;
3. prove (21) by the three cases \(e\ge sd\), \(0\le e<sd\), and \(e<0\);
4. prove the finite opponents-law estimate (26) and the cap-pin case split;
5. state the exact theorem as the zero-error corollary;
6. telescope the one-coordinate estimate over a supplied actual prefix chain;
   and
7. implement the interleaved ledger with \(\kappa_k\) as a positive part and
   prove its bound by the existing coordinate debt Lipschitz lemma.

Suggested public declarations are:

```text
quittingTerminalSemanticDebt_prefix_eq_max_endpoint_sub_mix
approxRoot_fixedDebtor_capNearSingleton_coordinateDebtDrop_ge
exactRoot_fixedDebtor_capNearSingleton_coordinateDebtDrop_ge
approxPrefixChain_capPin_visitCard_le
interleavedPrefixReentry_capPin_replenishment_ledger
```

The tropical sequence adapter should remain separate until that source export
has checked declarations. The static theorem must not acquire Fin4, global
minimum, stationary-profile, or root-absorption assumptions.

## Scope and nonclaims

- This is ordinary mathematics, not yet a Lean-checked theorem.
- The pointwise result applies to every finite player set, but the supplied
  conjecture-facing source adapter is currently Fin4.
- The roots are independent product roots against the literal prescribed
  payoff, not roots against the complete cap vector.
- The theorem gives one fixed coordinate debt expenditure and a vertical
  finite-visit budget. It does not regenerate the cap pin.
- The interleaved ledger permits arbitrary source reconstruction, but does not
  bound its replenishment. It proves that infinite recurrence has nonsummable
  semantic cost; it does not yet turn that cost into playable absorption or a
  punishment-floor Nash--Bellman return.
- No stationary equilibrium, terminal approximate Nash profile,
  uniform-equilibrium payoff, or positive-gap counterexample is constructed.
- The result is not a global atlas rank. Horizontal response and re-realization
  edges remain exactly the possible rank reset.
