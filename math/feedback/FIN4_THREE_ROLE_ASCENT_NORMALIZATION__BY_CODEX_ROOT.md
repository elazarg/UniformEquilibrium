# Review of source-faithful three-role ascent normalization

## Verdict

The packet contains a useful and apparently correct one-dimensional
normalization theorem for a strict three-role endpoint ascent. It does not
establish the claimed adapters to the canonical-pair support handoff or to the
strict maximal-cap ray. Those atlas transitions require data absent from
`ConcentratedCollisionThreeRoleEndpointLaw`.

The surviving result is worth retaining as a new normalized horizontal-ascent
node. It is not a consumer of that node and does not close the off-minimum paid
exit.

## Valid normalization core

Let `sigma_n` and `tau_n` be the retained source and pure-endpoint profiles,
differing only in the mover's action at the marked date. Interpolating that one
action probability gives literal profiles `sigma_(n,s)` for `s in [0,1]`.

The following steps are mathematically sound:

1. Prescribed payoff and every terminal-law coordinate are affine in `s`.
2. The mover's cap is constant because its opponents are unchanged, so its
   debt is affine.
3. For every nonmover, each fixed-response payoff is affine; its cap is a
   supremum of affine functions, and its debt is convex.
4. Reward boundedness gives a uniform Lipschitz estimate, including for the
   unrestricted caps. A finite-coordinate Arzela--Ascoli extraction therefore
   yields one continuous joint semantic/law ray `Z`.
5. `f(s)=D(Z(s))` is continuous and convex. Global minimality, `f(0)=D_*`, and
   strict ascent `f(1)>D_*` imply that its minimum set is an interval
   `[0,theta]`, with `theta<1` and strict debt ascent after `theta`.
6. If `theta>0`, the literal profiles at `theta` realize a new minimum joint
   point on the same ray. Affinity of the law retains the source marked atom
   with floor `(1-theta) rho` and the target routed atom with floor
   `theta rho`.
7. Exact reparameterization by `theta+(1-theta)s` preserves the full target and
   yields the stated mover-drop and recipient-rise estimates at the reduced
   resolution `rho'=(1-theta)rho`.

Thus the honest dichotomy is

```text
theta > 0:
  source-faithful minimum-point regeneration on the literal endpoint ray,
  followed by a rebased strictly ascending horizontal ray;

theta = 0:
  the incoming horizontal endpoint ray is already strictly ascending away
  from its minimum source.
```

The binary rightmost-minimum rank is a valid idempotent normalization of this
ray class. It does not by itself consume the rank-zero strict ray.

## Unsupported canonical-pair identification

The public three-role endpoint structure stores:

- `mover != owner`;
- `recipient != mover`;
- a marked nonsingleton coalition;
- a routed coalition obtained by forcing the mover's endpoint action; and
- a positive recipient-debt atom supplied by a payoff decoder.

It does **not** store:

- `recipient != owner`;
- membership of the owner or recipient in the marked coalition;
- membership of either role in the routed coalition;
- that the marked and routed coalitions are distinct;
- that their cardinalities are two and three; or
- that either side is `{owner,recipient}`.

Indeed, `HasQuittingEndpointDebtRecipientAtom` explicitly says that its
terminal label is selected by the payoff decoder rather than inherited from
the marked collision. The transfer orientation also permits the routed
coalition to equal the marked coalition when the forced endpoint action agrees
with the mover's membership.

Consequently the asserted identities

```text
canonicalPair = {owner, recipient},
marked/routed = canonicalPair and canonicalPair insert mover
```

do not follow from the inspected interface. The positive-`theta` arm therefore
does not yet enter `CanonicalPairMinimumEndpointSupportRankHandoff`.

## Unsupported maximal-ray identification

When `theta=0`, the construction yields a strict **horizontal one-date
endpoint interpolation**. A strict maximal-prefix ray is a different object:
it requires exact cap--Nash prefix roots, a maximal-absorption selection, its
autonomous semantic orbit, and the associated limiting-cap data.

Strict debt ascent along the one-date interpolation supplies none of those
facts. Therefore

```text
theta = 0 -> strict maximal-ray stall
```

is not proved. A new normalized horizontal-ascent node or a separate adapter
is required.

## Scope of the reparameterization

The literal identity

```text
partial(partial(sigma,theta),s)
  = partial(sigma,theta+(1-theta)s)
```

is valuable source provenance. Calling it a “backward compiler” should not be
read as a compiler for uniform payoffs, caps, or exact Nash--Bellman paths. It
only identifies the underlying behavioral profiles on the same horizontal
ray.

## Strongest retained conclusion

The packet gives a source-faithful rightmost-minimum normalization of every
strict three-role endpoint ascent. It reduces arbitrary ascent to a regenerated
minimum source plus a strictly normalized horizontal ray, without losing the
full target, roles, law, atom floors, or endpoint debt inequalities.

To connect this result to the existing Fin4 atlas, one still needs either:

1. additional checked incidence/cardinality hypotheses producing the
   canonical pair; or
2. a consumer or transition defined directly for the normalized horizontal
   ascent, without identifying it with the maximal cap-prefix ray.

## Sources inspected

- `ASCENT_NORM/FIN4_THREE_ROLE_ASCENT_NORMALIZATION.md`;
- `ASCENT_NORM/RESPONSE.md`;
- `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`;
- `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`; and
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionRecipientAtom.lean`.

No Lean or export status is assigned.
