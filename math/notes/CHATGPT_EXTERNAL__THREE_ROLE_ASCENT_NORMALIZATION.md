# Source-faithful normalization of a strict Fin4 three-role endpoint ascent

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; ordinary mathematics, pending its independent gate.

Source: supplied in `ephemeral/ASCENT_NORM/` and moved here without rewriting
the mathematical body.

## Statement

Let `source : FinFourMinimumAtomProducer reward bound`, let `packet` be its
source-attached concentrated packet, and let

```text
endpoint :
  ConcentratedCollisionThreeRoleEndpointLaw
    source.point.1 packet mover recipient
```

satisfy

```text
D(source.point.1) < D(endpoint.targetPoint.1).
```

There is a literal one-date partial-endpoint ray joining the endpoint's stored
source sequence to its stored target sequence.  Let `theta` be the rightmost
parameter on that same ray whose limiting total debt is the global minimum
`D_*`.

Then `theta < 1`, and exactly one of the following holds.

1. `theta = 0`.  The supplied endpoint is already a strict normalized endpoint
   ray: every positive partial endpoint is strictly above `D_*`.  It enters the
   strict maximal-ray-stall / strict endpoint-normalized-return node with the
   original source, roles, full endpoint sequence, law, routed atom, and
   quantitative floors.

2. `0 < theta`.  The ray point at `theta` is a new minimum joint semantic/law
   source on the same literal endpoint ray.  Rebasing the endpoint operation at
   `theta` preserves the full target, mover, recipient, routed terminal, and
   strict ascent.  It also preserves the standard Fin4 quantitative endpoint
   inequalities after replacing `resolution` by
   `(1-theta) * resolution`.  The rebased ray has no positive minimum prefix.
   Thus this is a regenerated minimum source with an intrinsic rank decrease
   `1 -> 0`.

For a genuine Fin4 three-role transfer, the checked role equations identify
the marked and routed coalitions as the canonical pair and its one-player
extension.  Consequently the positive-`theta` arm enters the canonical-pair
minimum-endpoint support handoff, while the zero-`theta` arm enters its strict
maximal-ray-stall arm.  The affine reparameterization below is the backward
compiler.

## 1. Literal partial endpoint ray

Write `sigma_n` for the endpoint's stored source profile and `tau_n` for its
stored pure endpoint profile.  They differ only in the mover's action at the
stored marked date.  For `s in [0,1]`, replace that one behavioral probability
by

```text
p_{n,s} = (1-s) p_n + s 1_endpointAction
```

and call the resulting actual profile `sigma_{n,s}`.  Thus

```text
sigma_{n,0} = sigma_n,
sigma_{n,1} = tau_n.
```

The construction changes neither the prefix before the marked date nor the
continuation after it.

For every player payoff and every terminal coalition law coordinate,

```text
u_i(sigma_{n,s})
  = (1-s) u_i(sigma_n) + s u_i(tau_n),

law(sigma_{n,s})
  = (1-s) law(sigma_n) + s law(tau_n).
```

For the mover, the unrestricted cap is unchanged because the opponents are
unchanged.  Hence the mover's debt is affine in `s`.

For `i != mover`, every fixed deviation payoff is affine in `s`; the
unrestricted cap is the supremum of those affine functions.  Therefore the
cap, and hence player `i`'s debt, is convex in `s`.

Reward boundedness gives a uniform Lipschitz bound for all these functions.
After one common subsequence, Arzela--Ascoli gives a continuous joint
semantic/law ray

```text
Z : [0,1] -> jointCarrier
```

with

```text
Z(0) = endpoint.sourceLimit,
Z(1) = endpoint.targetPoint.
```

The original source and target profile sequences remain the witnesses at the
two endpoints; `sigma_{n,s}` witnesses every intermediate point.

## 2. Total-debt convexity and the rightmost minimum

Let

```text
f(s) = D(Z(s)).
```

Every debt coordinate is convex except the mover coordinate, which is affine,
so `f` is continuous and convex.  Since `D_*` is the global minimum on the
joint carrier,

```text
D_* <= f(s)                  for every s in [0,1].
```

The endpoint fields give

```text
f(0) = D_*,
D_* < f(1).
```

The compact set

```text
M = {s in [0,1] | f(s) = D_*}
```

is nonempty.  Let `theta = max M`.  Then `theta < 1`.  Convexity shows

```text
f(s) = D_*    for 0 <= s <= theta,
D_* < f(s)    for theta < s <= 1.
```

Indeed, if `s <= theta`, convexity bounds `f(s)` above by the constant chord
joining `(0,D_*)` and `(theta,D_*)`, while global minimality bounds it below by
`D_*`.

This is the exact maximal minimum-return prefix; no unrelated minimizer is
introduced.

## 3. Positive atom floors at the normalized source

Let `M0` be the stored marked terminal and `R` the routed terminal.  The source
packet gives a positive source mass floor for `M0`, while the endpoint gives

```text
resolution <= Z(1).law (some R).
```

Affineness of the complete stopping law yields

```text
Z(theta).law (some M0)
  >= (1-theta) * resolution,

Z(theta).law (some R)
  >= theta * resolution.
```

Thus, when `0 < theta < 1`, the new minimum law retains both sides of the
literal endpoint toggle with explicit positive floors.  In particular it
contains the canonical pair atom, whichever side of the three-role toggle is
the pair.

## 4. Rebasing and preservation of the quantitative endpoint data

For `s in [0,1]`, define

```text
rebase_theta(s) = theta + (1-theta) s.
```

At profile level one has the exact identity

```text
partialEndpoint (partialEndpoint sigma_n theta) s
  = partialEndpoint sigma_n (rebase_theta(s)).
```

This is the backward compiler.  It is literal equality of behavioral profiles,
not merely equality of semantic limits.

Let

```text
rho' = (1-theta) * resolution.
```

The new source profile is `sigma_{n,theta}` and the full target remains
`tau_n`.  The marked source mass is at least `rho'`, and the full target routed
mass is at least `resolution`, hence at least `rho'`.

Let `d_i(s)` denote the limiting player debts on the ray.  Since the mover debt
is affine,

```text
d_mover(theta) - d_mover(1)
  = (1-theta) * (d_mover(0) - d_mover(1)).
```

Using the checked Fin4 endpoint inequality,

```text
d_mover(theta) - d_mover(1)
  >= (1-theta) * resolution^2 * D_* / 8
  >= rho'^2 * D_* / 8.
```

For the fixed recipient, convexity gives

```text
d_recipient(theta)
  <= (1-theta) d_recipient(0) + theta d_recipient(1),
```

and therefore

```text
d_recipient(1) - d_recipient(theta)
  >= (1-theta) * (d_recipient(1) - d_recipient(0))
  >= (1-theta) * resolution^2 * D_* / 64
  >= rho'^2 * D_* / 64.
```

So the same mover and recipient satisfy the standard quantitative endpoint
bounds after rebasing.  The strict target ascent is unchanged because the full
target is unchanged and the rebased source is again on the minimum fibre.

Moreover, for every `s > 0`,

```text
D(Z(rebase_theta(s))) > D_*.
```

Hence the rebased endpoint is strictly normalized.

## 5. Renewable finite rank

For an endpoint ray based at a minimum source define

```text
rayRank = 1
```

when it has a positive minimum-return prefix, and `rayRank = 0` otherwise.

If `theta > 0`, the incoming ray has rank `1`.  The rebased ray has rank `0`,
because every positive rebased parameter corresponds to a parameter strictly
larger than `theta`.  Therefore

```text
next.rayRank = 0 < 1 = incoming.rayRank.
```

This rank is renewable rather than a comparison with an ad hoc parent:
applying the same normalization to the rebased ray recomputes `theta = 0`.
Equivalently, rightmost-minimum normalization is idempotent.

If `theta = 0`, there is no source-return edge; the ray already enters the
strict normalized endpoint/maximal-ray-stall node.

## 6. Fin4 canonical-pair adapter

Unfolding the checked three-role transfer equations gives:

```text
routedTerminal = toggle marked mover,
marked ∪ routedTerminal = {owner, mover, recipient},
marked ∩ routedTerminal = {owner, recipient}.
```

The roles are distinct.  Since the marked row is a collision and the routed
terminal is nonempty, the two coalitions have cardinalities two and three.
Thus

```text
canonicalPair = {owner, recipient}
```

is exactly one side of the stored endpoint toggle.

At `theta > 0`, both sides have positive mass at the regenerated minimum law,
and `[0,theta]` is the literal maximal horizontal seam.  These are precisely
the support and provenance fields of the canonical-pair minimum-endpoint
support handoff.

At `theta = 0`, either the canonical pair is already supported at the incoming
minimum law, or it enters with the explicit law-density lower bound

```text
Z(s).law (some canonicalPair) >= s * resolution.
```

Together with strict debt ascent for every `s>0`, this is the strict
maximal-ray-stall entrance.

No target profile, routed atom, role, or continuation is discarded in either
case.

## 7. Lean interface

The useful checked interface should have the following shape (names can be
adapted to the declarations already in the atlas):

```lean
structure FinFourThreeRoleLiteralEndpointRay ... where
  point            : Set.Icc (0 : ℝ) 1 -> JointPoint
  profiles         : Set.Icc (0 : ℝ) 1 -> ℕ -> BehaviorProfile
  source_eq        : point 0 = endpoint.sourceLimit
  target_eq        : point 1 = endpoint.targetPoint
  profiles_tendsto : ...
  payoff_affine    : ...
  law_affine       : ...
  moverDebt_affine : ...
  otherDebt_convex : ...
  literal_rebase   : ...

structure FinFourThreeRoleNormalizedAscentHandoff ... where
  theta            : ℝ
  theta_mem        : theta ∈ Set.Ico 0 1
  minimum_prefix   : ∀ s ∈ Set.Icc 0 theta, D (ray.point s) = D_*
  strict_suffix    : ∀ s ∈ Set.Ioc theta 1, D_* < D (ray.point s)
  source           : FinFourMinimumAtomProducer reward bound
  endpoint         : ConcentratedCollisionThreeRoleEndpointLaw ...
  same_full_target : ...
  same_roles       : ...
  routed_floor     : ...
  rank_decrease    : theta > 0 -> nextRank < incomingRank
  backwardCompiler : ...

theorem
  FinFourThreeRoleRegenerationOrAscent.consume_strict_ascent
  (hstrict :
    D source.point.1 < D ascent.endpoint.targetPoint.1) :
  Nonempty (
    FinFourThreeRoleRankedMinimumRegeneration source ascent.endpoint
    ⊕ FinFourCanonicalPairStrictMaximalRayHandoff source ascent.endpoint)
```

The only analytic lemma not already contained in the endpoint object is the
common-subsequence extraction of the uniformly Lipschitz one-date cap
functions.  It is a finite-coordinate Arzela--Ascoli argument.  Everything
after that is one-dimensional convexity, exact profile rebasing, and finite
`Fin 4` set arithmetic.
