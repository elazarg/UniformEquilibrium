# Positive-Never half-release renewal has an exact q=0 endpoint

Author: `CODEX_MINER`

Status: **proved ordinary mathematics; two independent reviews PASS; internal
only.**  Reviews:
[`CODEX_EULER`](../feedback/CODEX_MINER__POSITIVE_NEVER_HALF_RELEASE_ZENO_ENDPOINT__BY_CODEX_EULER.md)
and
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__POSITIVE_NEVER_HALF_RELEASE_ZENO_ENDPOINT__BY_CODEX_RAMSEY.md).
This continues the reviewed actualizer boundary in
[`CODEX_MINER__POSITIVE_NEVER_UNIQUE_ALLCONTINUE_ACTUALIZER_BOUNDARY`](CODEX_MINER__POSITIVE_NEVER_UNIQUE_ALLCONTINUE_ACTUALIZER_BOUNDARY.md).
It eliminates the apparent infinite-dimensional ambiguity in repeated
same-owner half release: the entire renewal is one geometric stopping-law
chord converging to the full late-cap endpoint.  A minimum endpoint enters
the checked finite-atom causalization theorem.  An off-minimum endpoint is
not consumed, and an exact rational regression shows that strict unique
all-Continue cap geometry does not remove it without the global hard-residual
hypotheses.

## 1. Exact finite-source setting

Fix a finite quitting table and an actual independent profile `sigma` whose
marginal stopping laws have finite support plus `Never`.  Let `K` exceed
every finite support date.  Fix an owner `a` with positive singleton reward

```text
s=r_a({a})>0
```

and joint Never mass

```text
q=Law(sigma)(Never)>0.
```

Let `tau` change only player `a`: preserve its law below `K`, move all its
remaining Never mass to sure Quit at `K`, and Continue afterward.  Thus

```text
Law(tau)(Never)=0,
Law(tau)({a})=Law(sigma)({a})+q,
U_a(tau)-U_a(sigma)=s*q.                            (1.1)
```

Player `a`'s unrestricted cap depends only on the opponents and is unchanged,
so

```text
d_a(tau)=d_a(sigma)-s*q >= 0.                       (1.2)
```

The nonnegative remainder in (1.2) is the owner's exact finite-time premium
beyond the late singleton release.

## 2. The geometric chord is the whole renewal

For `k>=0`, let `sigma^k` change only `a` by the complete stopping-law
mixture

```text
a-law(sigma^k)=2^(-k)*a-law(sigma)
                 +(1-2^(-k))*a-law(tau).            (2.1)
```

The mixture is behaviorally realizable by the checked stopping-law mixture
strategy.  Equivalently, `sigma^(k+1)` is the equal mixture of the current
`a`-law in `sigma^k` and the fixed full-cap `a`-law in `tau`.  Thus this is
exactly repeated same-owner half release, not a correlated mixture of whole
profiles.

### Theorem 2.1 (exact Zeno endpoint)

For every `k`, writing `q_k=2^(-k)q`,

```text
Law(sigma^k)(Never)=q_k,                             (2.2)
Law(sigma^k)({a})=Law(sigma)({a})+(q-q_k),          (2.3)
U_a(sigma^k)=U_a(sigma)+s*(q-q_k),                 (2.4)
d_a(sigma^k)=d_a(sigma)-s*(q-q_k).                 (2.5)
```

Moreover the full terminal semantic pairs and laws converge:

```text
(Sem(sigma^k),Law(sigma^k)) -> (Sem(tau),Law(tau)). (2.6)
```

### Proof

The source and full-cap laws agree on every terminal path except the old
joint-Never event.  In the source branch that event remains Never; in the
cap branch it becomes singleton `{a}`.  Equations (2.2)--(2.4) follow by
linearity of the one-coordinate stopping-law mixture.  Own-cap invariance
gives (2.5).

The `a`-law in (2.1) converges in total variation to the full-cap law.  Every
prescribed payoff therefore converges.  For any other player and any fixed
behavioral deviation, the induced payoff changes by at most the same
total-variation error times twice a reward bound; this estimate is uniform
before taking the supremum.  Player `a`'s cap is constant.  Hence every
unrestricted cap converges as well, proving (2.6). `QED`

The construction can retain any old finite terminal atom occurring before
`K`.  Independently of that old atom, (2.3) creates a singleton `{a}` atom of
limiting mass at least `q` at the q=0 endpoint.

## 3. Telescoping the descent-or-transfer fork

At step `k`, the prescribed owner gain is

```text
g_k=s*(q_k-q_(k+1))=s*q_k/2.                        (3.1)
```

Apply the exact late-release debt identity to the partial replacement
`sigma^k -> sigma^(k+1)`.  Its standard split says either the sum of opponent
debt changes is greater than `g_k/2`, yielding the sharp three-label transfer,
or

```text
D(sigma^(k+1)) <= D(sigma^k)-g_k/2
                 = D(sigma^k)-s*q_k/4.              (3.2)
```

For `k>0`, the source already carries mass at the release date `K`, so the
published decoder's literal premise that every source atom precedes `K` is
not invoked verbatim.  Couple consecutive laws so their original finite
atoms and already deposited mass at `K` agree.  Only half of the residual
Never branch changes from `Never` to `K`; the common old `K` mass cancels in
every observer payoff difference.  The same `{a}`, `{b}`, and `{a,b}`
formulas, pure-time cap comparison, and constants therefore apply to every
partial step.

### Theorem 3.1 (finite transfer or paid q=0 endpoint)

If the transfer branch never occurs, then

```text
D(tau) <= D(sigma)-s*q/2.                           (3.3)
```

Consequently, if `D_*` is the global terminal-semantic debt minimum and

```text
D(sigma)-D_* < s*q/2,                               (3.4)
```

some finite half-release stage must enter the fixed-recipient three-label
transfer branch.

### Proof

Sum (3.2) for `k<N`:

```text
D(sigma^N)
 <= D(sigma)-(s/4)*sum_(k<N) q/2^k.
```

The geometric sum tends to `2q`.  Pass to the limit using (2.6) and
continuity of total debt to obtain (3.3).  Global minimality gives
`D_*<=D(tau)`, so (3.4) contradicts (3.3). `QED`

This is the exact summable potential.  There is no hidden infinite renewal
charge beyond the original singleton-weighted Never account.  The stronger
one-shot full-release inequality from the companion note forces a transfer
already when `D(sigma)-D_*<s*q`; Theorem 3.1 records what follows if one
insists on resolving the profile through the renewable half-release stages.

## 4. When the q=0 endpoint reaches the checked causal arm

Suppose now that `D_*>0` and the endpoint satisfies

```text
D(tau)=D_*.                                         (4.1)
```

The actual joint point `(Sem(tau),Law(tau))` is a minimum carrier point,
has zero Never coordinate, and by (1.1) has

```text
Law(tau)({a})>=q>0.                                 (4.2)
```

Therefore the checked theorem
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` applies
with terminal coalition `{a}`.  It produces arbitrarily deep exact cap--Nash
source words whose literal suffix retains that positive singleton atom and
whose front debts converge to `D_*`.

For a Lean handoff, first rewrite (4.1) as equality with the literal debt
infimum using
`quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum`.  Together
with `D_*>0`, this supplies the causal theorem's exact minimum and positivity
fields; no informal identification of `D_*` is needed.

This is an established producer, not a uniform-payoff consumer: the atom row
remains in the declared suffix rather than among the exact prefix roots.
Nevertheless, the infinite positive-Never renewal has genuinely terminated
in the already maintained q=0 causal-atom lane.

If instead

```text
D(tau)>D_*,                                         (4.3)
```

joint carrier causalization still realizes its finite atom in an actual
window, and `exists_capNashRootStack_retaining_positiveStage` retains the
atom behind arbitrarily deep exact prefixes.  But the front debt is not
known to approach `D_*`; the near-minimum conclusion of the checked theorem
uses (4.1) essentially.  Thus (4.3), not q=0 itself, is the precise survivor.

## 5. Debt support at the endpoint

Equation (1.2) gives the exact owner residual

```text
p_a=d_a(sigma)-s*q=d_a(tau)>=0.                     (5.1)
```

If `p_a=0`, owner `a` leaves the positive-debt support at the q=0 endpoint.
This is not automatically a checked support-rank descent: other players may
enter the support along the same chord, and (4.1) need not hold.  If (4.1)
does hold and no opponent support entry occurs, the endpoint has a literal
strict support subset and can be re-extracted as a smaller-cardinality
minimum tangent source.  Otherwise the exact residual is either the positive
finite-time premium `p_a>0`, off-minimum excess (4.3), or opponent support
entry/three-label transfer.

## 6. Exact strict-unique-all-Continue Zeno regression

The following rational two-player table shows that `q_k->0`, a retained
finite atom, strict singleton slack, and a unique all-Continue cap root can
coexist with (3.2) at every stage while the q=0 endpoint remains strictly
off the global minimum.  It is an interface regression, not a hard-residual
counterexample.

Use players `a,b` and rewards

```text
r({a})   = ( 1, 1),
r({b})   = ( 2, 0),
r({a,b}) = (-1,-1).                                 (6.1)
```

For `0<x<=1/2`, let player `b` Quit at date zero with probability `1/4` and
otherwise Never.  Let player `a` Quit at date one with probability `1-x` and
otherwise Never.  Then

```text
Law({b})=1/4,
Law({a})=3(1-x)/4,
Law(Never)=q(x)=3x/4.                               (6.2)
```

Pure-time comparison against all unrestricted behavioral deviations gives

```text
U(x)=(5/4-3x/4, 3(1-x)/4),
B(x)=(5/4,       1-x),
d(x)=(3x/4,      (1-x)/4),
D(x)=1/4+x/2.                                      (6.3)
```

For player `a`, any finite Quit after date zero gives `5/4`, immediate Quit
gives `1/2`, and Never gives `1/2`.  For player `b`, a Quit after player
`a`'s finite support or Never gives `1-x`, while immediate Quit gives zero
and collision at date one is nonpositive.  This proves the cap formulas in
(6.3), including the behavioral upgrade by pure-time extremality.

Against the tail `B(x)`, Continue strictly dominates Quit at the one-stage
root for both players.  If player `b` Quits with probability `z`, player
`a`'s Continue-minus-Quit endpoint difference is

```text
1/4+(11/4)z>0.                                      (6.4)
```

If player `a` Quits with probability `w`, player `b`'s difference is

```text
2w+(1-w)(1-x)>0.                                    (6.5)
```

Thus all Continue is the unique exact product-root Nash equilibrium, with
uniform strict singleton gaps at least `1/4` for `0<x<=1/2`.

Repeated half release of `a` replaces `x` by `x/2` at the semantic/law
level (the finite Quit mass may be split over successively later dates, which
does not change (6.2)--(6.3)).  Hence every step is strict debt descent:

```text
D(x/2)-D(x)=-x/4.                                   (6.6)
```

Yet the endpoint has

```text
q(0)=0,
Law({a})=3/4,
D(0)=1/4.                                           (6.7)
```

The global minimum is zero: the profile in which `b` Quits surely at date
zero and `a` Continues has zero unrestricted debt.  Consequently

```text
[D(x)-D_*]/q(x)=1/(3x)+2/3 -> infinity.             (6.8)
```

This disproves any universal normalized-`E/q` contradiction or claim that
the strict unique-root fields force the q=0 endpoint onto the minimum fiber.
The table has a terminal equilibrium and therefore no positive global
terminal gap; it does not refute a theorem using the full Fin4 hard residual.

## 7. Source audit and exact remaining implication

Checked declarations inspected:

- `quittingStoppingLawMixtureBehaviorStrategy` and
  `quittingTerminalSemanticDebt_stoppingLawMixture_le` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
- `exists_jointRealizers_finiteWindow_positiveStage_of_lawMass_pos`,
  `exists_capNashRootStack_retaining_positiveStage`, and
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- the unrestricted pure-time cap equality used throughout the terminal
  semantic layer; and
- the reviewed full and partial late-release identities in the companion
  actualizer note.

The exact full-hard-residual survivor is now:

```text
q_k -> 0 along an exact renewable actual-source chord,
positive singleton atom retained at the q=0 endpoint,
but D(endpoint)>D_* and the endpoint cap port may again be inert.          (7.1)
```

Eliminating (7.1) requires a theorem using global terminal-gap/hard-residual
data to bring the off-minimum finite-atom endpoint to the minimum fiber or to
turn its causal atom into an admissible charged return.  Neither positivity
of the atom, strict singleton slack, unique all-Continue cap roots, nor the
normalized excess `E/q` suffices by itself.

## 8. Requested review

Please check the geometric stopping-law identity, full semantic/cap
convergence, telescope constant `s*q/2`, exact rational cap table,
strict-dominance root calculation, and the minimum hypothesis in the causal
handoff.  In particular, distinguish the actual q=0 endpoint theorem from a
claim that every cross-source regenerated sequence lies on one fixed chord.
