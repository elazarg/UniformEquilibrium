# Hidden-selector singleton passport and information-gap localization

Author: external `ChatGPT` contribution supplied by the user

Independent review:
[`CODEX_ROOT`](../feedback/CHATGPT_EXTERNAL__HIDDEN_RESET_VALUE_OF_INFORMATION_PASSPORT__BY_CODEX_ROOT.md)

Current status: the mathematics below passed independent review. It is kept
internal because the flat charged-circulation exit has been removed from the
active frontier by support-rank descent, and no theorem presently composes
this packet into an active paid-near-return or four-player full-support
consumer. The missing item is an importance/adapter gate, not a mathematical
lemma in the statements below.

## Exact setting

Let `I` be a nonempty finite player set and let `r` be a finite quitting-game
reward table. Terminal outcomes include every nonempty first-quitter
coalition and `Never`. Assume every reward coordinate has absolute value at
most `M`.

For a behavioral profile `x`, write

```text
U_i(x) = prescribed terminal payoff of player i,
B_i(x) = sup_alpha U_i(alpha,x_-i),
d_i(x) = B_i(x)-U_i(x),
D(x)   = sum_i d_i(x).
```

The supremum in `B_i` ranges over all unilateral behavioral strategies. In a
quitting game it may be approximated arbitrarily closely by a deterministic
pure quit time in `N union {Never}`.

Fix a finite reset set `A subseteq I`, a source profile `x`, a replacement
strategy `beta_a` for every `a in A`, and an inner reset weight
`lambda in [0,1]`. Let `x_a^lambda` be the behavioral realization of the
complete-stopping-law mixture

```text
(1-lambda) Law(x_a) + lambda Law(beta_a).
```

For `S subseteq A`, let `x^S` use `x_a^lambda` exactly for `a in S` and use
the source strategy in every other coordinate.

Choose independent private outer selector bits with probabilities
`q_a in [0,1]`. Their face weights are

```text
w(S)=product_(a in S) q_a * product_(a in A\S) (1-q_a).
```

The hidden profile `bar x` behaviorally realizes the independent complete-law
mixtures between `x_a` and `x_a^lambda` with weights `q_a`. The selector bits
are not observed by a deviating player. This is ordinary private behavioral
randomization, not a public correlating device.

## Theorem A: exact hidden-selector debt identity

For every player `i`,

```text
U_i(bar x) = sum_S w(S) U_i(x^S),                         (1)
B_i(bar x) <= sum_S w(S) B_i(x^S).                       (2)
```

Define the information gap

```text
G_i = sum_S w(S) B_i(x^S)-B_i(bar x).
```

Then `G_i>=0` and

```text
d_i(bar x)=sum_S w(S)d_i(x^S)-G_i.                       (3)
```

If `alpha_i` is `epsilon_i`-optimal at `bar x` and

```text
R_i(S)=B_i(x^S)-U_i(alpha_i,x^S_-i),
```

then

```text
sum_S w(S)R_i(S) <= G_i+epsilon_i.                       (4)
```

Consequently every face of weight at least `q>0` satisfies

```text
R_i(S) <= (G_i+epsilon_i)/q.                             (5)
```

### Proof

Successive complete-law affinity gives (1). The same affinity holds after
fixing any unilateral deviation `alpha_i`; the bit in player `i`'s own
coordinate disappears because that complete strategy has been replaced.
Therefore

```text
B_i(bar x)
 = sup_alpha sum_S w(S)U_i(alpha,x^S_-i)
 <= sum_S w(S)sup_alpha U_i(alpha,x^S_-i),
```

which is (2). Subtracting (1) gives (3). Substituting the fixed
`epsilon_i`-optimal deviation into the affine identity and rearranging gives
(4). Every regret is nonnegative, so (5) follows.

## Theorem B: uniform Boolean-cube remainder

Suppose `S subseteq A` and `a notin S`. The profiles `x^S` and `x^(S+a)`
differ by one complete-law reset of weight `lambda`. Then

```text
|U_i(x^(S+a))-U_i(x^S)| <= 2 M lambda,
|B_i(x^(S+a))-B_i(x^S)| <= 2 M lambda.                 (6)
```

The cap `B_a` is independent of player `a`'s prescribed strategy. Hence

```text
|d_a(x^(S+a))-d_a(x^S)| <= 2 M lambda,
|d_i(x^(S+a))-d_i(x^S)| <= 4 M lambda  when i!=a,      (7)
```

and, with `N=|I|`,

```text
|D(x^(S+a))-D(x^S)| <= L_D lambda,
L_D=(4N-2)M.                                           (8)
```

For four players, `L_D=14M`.

For a function `F:2^A -> R`, define

```text
partial_T F(empty)
  = sum_(R subseteq T)(-1)^(|T|-|R|)F(R).
```

If `q_a=h m_a`, where `m_a>=0`, `0<h<=1`, and `h m_a<=1`, then

```text
sum_S w_h(S)D(x^S)
 = D(x^empty)
   + h sum_a m_a[D(x^{a})-D(x^empty)]
   + R(h),                                               (9)
```

where

```text
|R(h)| <= L_D C(m) h^2 lambda,                         (10)
C(m)=sum_(T subseteq A, |T|>=2)
       2^(|T|-1) product_(a in T)m_a.
```

### Proof

Every terminal payoff lies in `[-M,M]`, so complete-law affinity gives the
first inequality in (6). Every fixed-deviation payoff has the same modulus;
taking its supremum preserves the modulus and gives the second inequality.
Equation (7) follows by subtraction and by invariance of the owner's cap.
Summing gives (8).

The exact product-Bernoulli Möbius formula is

```text
sum_S w(S)F(S)
 = sum_(T subseteq A)(product_(a in T)q_a)
     partial_T F(empty).                               (11)
```

For nonempty `T`, choose `a in T`. Its Boolean difference is a signed sum of
`2^(|T|-1)` edges `R -> R+a`, so (8) gives

```text
|partial_T D(empty)| <= 2^(|T|-1)L_D lambda.           (12)
```

Separate the empty and singleton terms in (11), substitute `q_a=h m_a`, and
bound all terms of degree at least two using (12). This is (9)--(10). No
differentiability or common cap maximizer is assumed.

## Theorem C: flat-balance singleton passport

Consider sequences of source profiles `x_n`, inner reset scales
`lambda_n>0`, and replacements `beta_(n,a)` for `a in A`. Write `x_n^S` for
the corresponding faces. Let `D_*` be the global minimum of total terminal
semantic debt and suppose

```text
delta_n=[D(x_n^empty)-D_*]/lambda_n -> 0,              (13)
Delta_(n,a)(i)
 =[d_i(x_n^{a})-d_i(x_n^empty)]/lambda_n
 -> tau_a(i).                                          (14)
```

Fix weights `m_a>=0` satisfying the coordinatewise flat balance

```text
sum_a m_a tau_a(i)=0                    for every i.    (15)
```

There is a sequence `h_n>0` such that

```text
h_n -> 0,
h_n m_a<=1,
delta_n/h_n -> 0.                                      (16)
```

Use outer probabilities `q_(n,a)=h_n m_a` and let `bar x_n` be the hidden
profile. Its information gaps satisfy

```text
0<=sum_i G_(n,i)=o(h_n lambda_n),
G_(n,i)=o(h_n lambda_n)                for every i.    (17)
```

For every player `i`, choose a pure quit time `t_(n,i)` within
`epsilon_n=o(h_n lambda_n)` of `B_i(bar x_n)`. Then

```text
B_i(x_n^empty)-U_i(t_(n,i),(x_n^empty)_-i)
  = o(lambda_n),                                       (18)
max_(a:m_a>0)
 [B_i(x_n^{a})-U_i(t_(n,i),(x_n^{a})_-i)]
  = o(lambda_n).                                       (19)
```

No analogous first-order estimate is asserted on arbitrary doubleton or
higher-dimensional faces.

### Proof

Because `delta_n>=0` and tends to zero, choose `h_n` tending slowly enough to
zero that `delta_n/h_n->0`, while imposing the finitely many bounds
`h_n m_a<=1`. A capped version of
`sqrt(delta_n)+1/sqrt(n+1)` works.

The singleton term in (9), divided by `h_n lambda_n`, tends to zero by
(14)--(15); (10) is `O(h_n^2 lambda_n)`. Equations (13) and (16) therefore
give

```text
sum_S w_n(S)D(x_n^S)-D_*=o(h_n lambda_n).              (20)
```

The hidden mixture is an actual profile, so `D(bar x_n)>=D_*`. Summing (3)
over players proves (17). Equation (4) gives total weighted face regret
`o(h_n lambda_n)`. The empty face has weight tending to one. Every fixed
singleton with `m_a>0` has weight at least `m_a h_n/2` eventually. Dividing
the weighted regret bound by those weights proves (18)--(19), uniformly over
the finite positive support of `m`.

A `k`-face has only order `h_n^k` weight, yielding at best
`o(lambda_n h_n^(1-k))`; this proves the stated boundary.

## Theorem D: information gaps produce witness-switch rectangles

Let `x^0,x^1` be two actual profiles differing only in one opponent's
strategy. For a pure quit time `t`, set

```text
F_b(t)=U_i(x^b[i<-t]),
B_b=sup_t F_b(t).
```

For `q in (0,1)`, define

```text
B_q=sup_t[(1-q)F_0(t)+qF_1(t)],
J=(1-q)B_0+qB_1-B_q.
```

If `t_0,t_1` are `epsilon`-optimal at the two endpoints, then

```text
F_1(t_1)-F_1(t_0) >= (J-epsilon)/q,                   (21)
F_0(t_0)-F_0(t_1) >= (J-epsilon)/(1-q).               (22)
```

If `J>epsilon`, the witnesses differ. At the endpoint where the temporally
later witness wins, the checked pure-time first-disagreement decoder supplies
a literal paid first-disagreement row. This includes `Never` as the later
witness.

For finitely many independent bits, reveal them successively. If the total
information gap for player `i` is at least `gamma`, some opponent bit and some
fixed preceding-bit context have conditional one-bit gap at least
`gamma/|A|`. Unrevealed later bits remain behaviorally mixed, so the one-bit
conclusion applies at actual behavioral profiles.

### Proof

Test `t_0` in `B_q`, use endpoint near-optimality, and rearrange to obtain
(21). Testing `t_1` gives (22). Pure quit times are totally ordered, so one of
these inequalities is a positive gain for the later time when `J>epsilon`.

For many bits, let `V_k` be the expected cap after revealing the first `k`
bits. Convexity makes every increment nonnegative and

```text
G_i=V_|A|-V_0=sum_k(V_k-V_(k-1)).                     (23)
```

One increment is at least `gamma/|A|`; averaging over earlier assignments
selects a context with at least that conditional gap. The bit cannot be
player `i`'s own selector, because its cap ignores its prescribed strategy.

## Corollary E: flat-no-entry observer/debtor alignment

Let a positive-minimum tangent column for mover `a` satisfy

```text
tau_a(a)=-d_a(base)<0,
sum_i tau_a(i)=0,
```

and assume the checked no-support-entry condition. Some `o!=a` has
`tau_a(o)>0`. The checked theorem
`QuittingPositiveMinimumDebtTangentFamily.mem_active_of_tangent_pos_of_noEntry`
then implies `d_o(base)>0`. Along the realizing sources and hidden profiles,

```text
d_o(x_n^empty)->d_o(base)>0,
d_o(bar x_n)->d_o(base)>0.                             (24)
```

Thus the positive off-diagonal atom observer is already a positive debtor at
the label level. The remaining problem is not equality of two finite labels.

Moreover, let `t_n` be the common source/singleton witness and measure its
regret `rho_n` at the full replacement endpoint. Along a subsequence either

1. `rho_n->0`, so `t_n` is approximately optimal at the source, inner
   singleton face, and full endpoint; or
2. `liminf rho_n>0`, in which case affinity of two fixed-witness payoff charts
   gives a source-to-full-endpoint witness switch, and the full endpoint
   carries a fixed-positive paid first-disagreement row.

### Proof

The negative diagonal and zero column sum force a positive off-diagonal
coordinate. The cited checked theorem supplies activity under no entry.
One-coordinate debt Lipschitzness and telescoping the outer selector mixtures
give

```text
|d_o(bar x_n)-d_o(x_n^empty)|
 <=4M h_n lambda_n sum_a m_a ->0.
```

For the endpoint alternative, parametrize the complete-law mover segment by
`s in [0,1]`, with the inner face at `s=lambda_n`. If `t'_n` is nearly
optimal at `s=1`, the difference between the fixed-witness payoff charts for
`t'_n` and `t_n` is affine in `s`. Near-optimality of `t_n` at
`s=lambda_n` and a positive endpoint regret orient the two witnesses in
opposite directions; the endpoint advantage is bounded away from zero in the
second case. Apply Theorem D and the checked paid-row decoder.

## Exact boundary change

The packet proves three corrections to the former frozen-cube account:

1. the multi-reset total-debt remainder is uniformly `O(h^2 lambda)` despite
   cap switching;
2. flat balance yields one common pure-time chart on the source and all
   positive-weight singleton faces;
3. in the flat no-entry branch, observer/debtor label alignment is automatic,
   while information curvature localizes to a witness rectangle rather than
   necessarily to a two-reset cap square.

The remaining statement is co-realization. One must put the positive observer
debt, witness comparison, nonvanishing reach floor, and persistent labelled
clocks on one actually reached history, or embed a fixed-positive paid row in
a punishment-floor-admissible payoff near-return.

This was a strict narrowing of the former conditioned-reset/circulation
analysis. It is not currently a strict narrowing of an indexed live question:
support-rank descent has eliminated flat charged circulation as an independent
exit, and the result does not construct the paid near-return required by
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md` or consume the hard residual
in `questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.

## Source correspondence and novelty audit

The proof uses checked components from:

- `quittingStoppingLawMixtureBehaviorStrategy` and complete-law payoff
  affinity in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMixture.lean`;
- simultaneous reset profiles and unilateral passport alternatives in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSimultaneousResetMinimumDichotomy.lean`;
- `QuittingPositiveMinimumDebtTangentFamily.source_excess_over_scale_tendsto_zero`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
- fixed-deviation reset-cube identities in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingPositiveMinimumDebtTangentFamily.mem_active_of_tangent_pos_of_noEntry`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/PositiveDebtTangentCycle.lean`;
- the witness-switch and common-passport regressions in
  `TerminalSemanticSimultaneousMixtureWitnessSwitchRegression.lean` and
  `TerminalSemanticCommonWitnessPassportRegression.lean`.

Those files supply the one-coordinate and regression ingredients. A narrow
search found no declaration packaging the independent product-selector debt
identity, uniform total-debt Möbius remainder, singleton-star common passport,
and no-entry observer/debtor alignment. No external-paper claim is used.

## Boundary tests

1. With one hidden bit and two witnesses, the table

   ```text
                t0       t1
   z=0           0      -lambda
   z=1         -lambda    0
   ```

   has endpoint caps zero and hidden cap `-lambda/2`. Its positive
   information gap survives after adding irrelevant reset coordinates, while
   all cap squares in those coordinates vanish. Thus Theorem D cannot be
   strengthened to an information-gap-to-two-reset-square theorem using only
   convexity and affinity.
2. A `k`-face has selector weight of order `h^k`. Equation (4) then gives only
   `o(lambda h^(1-k))`, showing exactly why Theorem C stops at singleton
   faces.
3. A positive gap of order `h_n lambda_n` may yield a paid-row gain tending to
   zero. It does not meet the fixed-positive gain required by the paid
   near-return producer.
4. The selected conditional bit context need not be reached from the original
   profile. None of the proofs preserves reach floors, punishment-floor
   admissibility, Bellman edges, or labelled survival clocks.

## Lean handoff

The narrow implementation should first formalize the reusable finite lemmas,
without introducing a chronology structure:

```text
quittingHiddenStoppingLawSelectorProfile
quittingHiddenSelector_informationGap
quittingHiddenSelector_debt_eq_average_sub_informationGap
quittingHiddenSelector_weighted_faceRegret_le
quittingStoppingLawResetCube_totalDebt_edge_lipschitz
quittingStoppingLawResetCube_expectedDebt_mobius_remainder
exists_commonPureTimePassport_source_singletons_of_flatBalance
exists_paidFirstDisagreementRow_of_oneBit_informationGap
active_observer_of_flat_noEntry_hiddenSelector
```

Likely dependencies are the stopping-law mixture, tangent-family,
positive-debt tangent-cycle, and paid-first-disagreement files listed above,
plus the existing finite Boolean Möbius adapter. Finite tests should include
the one-bit/two-witness falsifier and the `Fin 4` constant `14M`.

No theorem should assert reachability of a selector context, a common witness
on higher faces, fixed positive paid gain from an asymptotically small
information gap, punishment-floor admissibility, or chronological clocks.

## Scope and nonclaims

This packet does not prove a uniform-equilibrium payoff, a paid admissible
payoff near-return, conditioned packet reprojection, persistent two-label
hazards, or the four-player conjecture. It does not use public randomization
or restrict the deviator. Its complete contribution is the hidden-selector
identity, uniform Möbius remainder, singleton passport, information-gap
localization, and flat-no-entry label alignment stated above.
