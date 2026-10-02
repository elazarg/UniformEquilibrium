# Independent review of the positive-Never half-release Zeno endpoint

Reviewer: **CODEX_RAMSEY**  
Source: [`CODEX_MINER__POSITIVE_NEVER_HALF_RELEASE_ZENO_ENDPOINT.md`](../notes/CODEX_MINER__POSITIVE_NEVER_HALF_RELEASE_ZENO_ENDPOINT.md)  
Verdict: **PASS, with two proof-writing handoffs**  
Disposition: **internal only**.  The note correctly identifies the exact
endpoint of repeated same-owner half release and a finite-transfer threshold.
Its strict off-minimum endpoint remains a boundary, not a `FIN4_BT_QUESTION`
consumer or an iterable rank reduction.

## Claim reviewed

Starting with a finite-support-plus-`Never` actual profile `sigma`, an owner
`a` with singleton reward `s=r_a({a})>0`, and joint Never mass `q>0`, let
`tau` move all of `a`'s remaining Never clock to one late finite date.  The
note claims that repeated equal stopping-law mixtures with this same endpoint
form one geometric chord `sigma^k -> tau`, with residual Never mass
`q_k=2^{-k}q`.  If the opponent-transfer arm never occurs, total debt falls by
at least `s q/2`; hence excess below that amount forces a transfer at a finite
stage.  If the endpoint is a positive global minimum, its new singleton atom
feeds the checked minimum-law causal-suffix theorem.  A rational two-player
example shows that the endpoint can instead remain strictly off-minimum even
under strict singleton separation and a unique all-Continue cap root.

All substantive claims pass.

## 1. Geometric stopping-law chord and endpoint

Holding the opponents fixed, the complete stopping law of `a` at stage `k`
is

```text
ell_k = 2^{-k} ell_sigma + (1-2^{-k}) ell_tau.
```

Therefore

```text
ell_{k+1}=(ell_k+ell_tau)/2.
```

This is a mixture of one player's complete stopping laws, not a correlated
mixture of whole profiles.  The checked construction
`quittingStoppingLawMixtureBehaviorStrategy` realizes it behaviorally.  Since
`sigma` and `tau` differ only on the old joint-Never event, whose outcome is
changed from `Never` to `{a}`, affine terminal-law transport gives exactly

```text
Law(sigma^k)(Never)=2^{-k}q,
Law(sigma^k)({a})=Law(sigma)({a})+(1-2^{-k})q,
U_a(sigma^k)=U_a(sigma)+s(1-2^{-k})q.
```

Player `a`'s unrestricted cap depends only on the opponents, so it is fixed
along the chord and its debt falls by the same amount.  For every other
player, coupling the changed `a` clock bounds every behavioral-deviation
payoff uniformly by twice the reward bound times the marginal total-variation
distance.  Taking the supremum preserves this estimate.  Thus both prescribed
payoffs and unrestricted caps converge, proving the full semantic/law
convergence to `(Sem(tau),Law(tau))`.

The endpoint identities are also exact:

```text
Law(tau)(Never)=0,
Law(tau)({a})=Law(sigma)({a})+q,
d_a(tau)=d_a(sigma)-s q >= 0.
```

The last nonnegativity is not an extra assumption: it follows because the
left side is a semantic debt.

## 2. Telescope and finite transfer threshold

At stage `k`, the moved Never mass is `q_k/2`, so the owner payoff gain and
owner debt loss are

```text
g_k=s q_k/2.
```

Writing `T_k` for the sum of the other players' debt changes gives the exact
identity

```text
D(sigma^{k+1})-D(sigma^k)=-g_k+T_k.
```

If `T_k<=g_k/2`, then

```text
D(sigma^{k+1}) <= D(sigma^k)-s q_k/4.
```

If this arm holds at every stage, summing and using
`sum_k q_k=2q`, followed by semantic convergence, yields

```text
D(tau) <= D(sigma)-s q/2.
```

Consequently `D(sigma)-D_*<s q/2` forces the positive opponent-transfer arm
at some finite stage.  The note correctly describes `s q/2` as a guaranteed
debt drop in the no-transfer arm, not as an unconditional equality for total
debt.

### Proof-writing handoff: the repeated partial decoder

The first late release uses a cutoff strictly beyond the finite support of
`sigma`.  After that step, however, `sigma^k` already has some mass at the
chosen release date `K`.  Thus the published sharp late-release statement,
when read with its literal “all source finite atoms before `K`” hypothesis,
cannot simply be invoked verbatim at every `k`.

The required extension is valid and costs no constant.  Couple the two
successive marginal laws so that they agree on the original finite atoms and
on the mass already placed at `K`; only half of the remaining Never branch is
changed from `Never` to `K`.  For an observer's pure time:

- before `K`, the changed branch is preempted and contributes zero difference;
- at `K`, after `K`, or at `Never`, the unchanged old `K` mass cancels from
  the source-target difference; and
- on the changed branch the same `{a}`, `{b}`, `{a,b}` formulas as in the
  sharp decoder remain exact.

Pure-time extremality then gives the same prescribed/cap-response split and
the same factors.  The author should spell out this cancellation extension in
any formal handoff; it is not a mathematical objection to Theorem 3.1.

## 3. Minimum endpoint and causal-suffix adapter

Because `tau` is an actual profile, its semantic/law point lies in the joint
carrier.  If

```text
D(tau)=D_*>0,
```

then its semantic coordinate is a global carrier minimum and
`Law(tau)({a})>=q>0`.  The hypotheses of
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`
are therefore satisfied with terminal coalition `{a}`.

The Lean-facing proof should explicitly rewrite the minimum value using
`quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum` from
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
That supplies both the theorem's equality with the literal debt infimum and,
from `D_*>0`, its `hinf` field.  This is the second proof-writing handoff.

The stated output is scoped correctly: the positive singleton atom survives
in the literal suffix behind arbitrarily deep exact cap-root stacks; it is
not asserted to be a prefix root, prescribed-payoff Bellman edge, paid row,
or return.  If `D(tau)>D_*`, ordinary joint-law causalization and positive-stage
retention remain available, but the near-minimum front-debt conclusion does
not.  This is precisely the unconsumed endpoint.

The support statement is likewise sound.  If
`d_a(tau)=d_a(sigma)-s q=0`, `a` leaves the debt support.  A strict support
reduction requires both endpoint minimality and absence of a newly positive
opponent coordinate.  Under those extra facts,
`exists_positiveMinimumDebtTangentFamily_of_pair` may be reapplied to that
same minimum semantic pair.  No unconditional or iterable rank descent is
claimed.

## 4. Rational two-player regression

For

```text
r({a})=(1,1),  r({b})=(2,0),  r({a,b})=(-1,-1),
```

with `b` quitting at date zero with probability `1/4` and `a` quitting at
date one with probability `1-x`, direct outcome enumeration gives

```text
U=(5/4-3x/4, 3(1-x)/4),
B=(5/4,       1-x),
d=(3x/4,      (1-x)/4),
D=1/4+x/2.
```

The cap calculation is genuinely unrestricted: pure-time extremality reduces
arbitrary behavioral deviations to the displayed finite times and `Never`.
For `a`, every finite time after date zero pays `5/4`, while date zero and
`Never` pay `1/2`.  For `b`, every time strictly after `a`'s last finite atom,
and `Never`, pays `1-x`; the collision time is nonpositive.

Against tail `B(x)`, the Continue-minus-Quit differences are exactly

```text
a: 1/4+(11/4)z,
b: 2w+(1-w)(1-x),
```

so every exact product root is all Continue.  Partial late release changes
only the total proper mass of `a`; splitting it across later finite dates
does not alter these payoff/cap formulas.  Hence `D(x/2)-D(x)=-x/4`, while
the endpoint has debt `1/4`.  The profile with `b` surely quitting at date
zero and `a` continuing has zero debt, so `D_*=0` and

```text
[D(x)-D_*]/q(x)=1/(3x)+2/3.
```

This exactly refutes a normalized excess/Never-mass bound or a local claim
that unique all-Continue cap geometry puts the endpoint on the minimum
fiber.  It has a terminal equilibrium and no positive terminal gap, so it
does not refute a theorem using the Fin4 hard residual.

## Final assessment

**PASS.**  The geometric chord, convergence, `s q/2` telescope, finite
transfer threshold, endpoint atom, minimum-law causal adapter, and rational
regression all survive independent falsification.  Before formalization,
state the repeated-partial decoder's old-`K` cancellation and insert the
literal-infimum rewrite named above.  The result should remain internal: it
terminates the apparent same-owner Zeno ambiguity, but its strict off-minimum
`q=0` endpoint supplies no checked return, terminal approximation, or
regenerating well-founded descent.
