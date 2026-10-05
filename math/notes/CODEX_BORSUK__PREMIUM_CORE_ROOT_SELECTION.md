# Exact tests for premium-core root selection

Owner: CODEX_BORSUK.

Status: complete exact boundary test in ordinary mathematics; not checked in
Lean. The independent review of MORSE Sections 10–13 is in
[`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_BORSUK.md`](../feedback/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_BORSUK.md).
That review accepts the stated four-player existence class. This notebook
adds a four-player fixture with a positive participant premium outside its
greatest premium core, checking that the extension really retains such
premiums. It asserts no unrestricted negative example or full-conjecture
solution.

## Exact question

Can a four-player table simultaneously have nonnegative own singletons and
participant premiums, greatest premium core `{0,1}`, a core-only exact root
whose successor is strictly above every singleton, and an exact root where a
positive-premium outsider is active but a different outsider pins the
successor to the original singleton lower boundary?

Yes. All roots below use independent Bernoulli Quit choices. Root annotations
are numerical continuations, not supplied behavioral strategies. Exact Nash
means each prescribed coordinate equals the larger pure-action endpoint.
The calculations concern the full root game, including every coalition; the
equilibrium conclusion comes only through the separately reviewed consumer.

## Complete reward table by formula

Define the three-coordinate vectors `b(T)` for nonempty `T⊆{0,1,2}`:

| T | b(T) |
| --- | --- |
| {0} | (1,−1,3) |
| {1} | (0,0,3) |
| {2} | (3,3,0) |
| {0,1} | (2,1,−1) |
| {0,2} | (1,3,0) |
| {1,2} | (3,0,0) |
| {0,1,2} | (1,0,0) |

For every nonempty `S⊆{0,1,2,3}`, put `T=S∩{0,1,2}`. Initially set
`(r₀(S),r₁(S),r₂(S))=b(T)` if `T` is nonempty, and `(0,0,0)` otherwise.
Override `r₂(S)=1` whenever `{2,3}⊆S`. Finally set `r₃(S)=0` if `3∈S`,
and `r₃(S)=1` otherwise. This specifies all fifteen reward vectors.

The singleton vector is `s=(1,0,0,0)`. Every participant premium is
nonnegative. Player 3 is flat on every participant coalition. After removing
3 from the premium calculation, player 2 is flat. The remaining pair has
premiums `r₀({0,1})−s₀=r₁({0,1})−s₁=1`. Thus the only premium trap is
`{0,1}`, whereas player 2 has premium one on every coalition containing both
2 and 3. In particular the globally constant-outsider hypothesis fails.

## Exact roots and determinant

At `v=(2,1,−1/10,1)`, take `p=(1/3,1/3,0,0)`. Its Quit-minus-Continue
gaps and successor are

    gaps(p) = (0,0,−53/45,−1),
    T_p(v) = (4/3,1/3,53/45,1).

Hence `p` is exact Nash and its successor is strictly above `s` in every
coordinate. Both outsiders strictly Continue. For the full clipped map
`F(q)ₖ=min(1,max(0,qₖ+gapₖ(q)))`, the derivative of `q−F(q)` at `p` is

    [  0   −3    2   −4/3 ]
    [ −3    0    3   −2/3 ]
    [  0    0    1     0  ]
    [  0    0    0     1  ].

Its determinant is `−9`. The nonzero outsider columns are retained; they
do not change the determinant. At the same annotation, `q=(0,0,1,0)` has

    gaps(q) = (−2,−3,1/10,−1),
    T_q(v) = (3,3,0,1),

so it is another exact Nash root, returning through player 2's coordinate.

Now use `u=(2,1,1,−1)` and `q=(0,0,1/2,1/2)`. Direct calculation gives

    gaps(q) = (−1,−7/4,0,0),
    T_q(u) = (2,7/4,1/2,0).

This root is exact Nash. Its active player 2 has Quit endpoint `1/2>s₂`,
because player 3 may join. Its active player 3 has Quit endpoint zero and
pins the actual successor to the original lower boundary. Thus the support
argument must find a flat member of the actual support; it cannot assume
that every peeled outsider remains flat once other outsiders activate.

All displayed identities were independently recomputed with Python's exact
`Fraction` arithmetic by enumerating the opponent coalitions in the two
pure-action endpoints. The finite trap enumeration returned only `{0,1}`.
These computations check this fixture; the review's general argument does
not depend on experiments.

## Source and next check

The bounded route began with `docs/TOOLKIT.md`, then the literal root,
ambient-degree, reward-closure, and Fin4 polynomial declarations listed in
the linked review. Also inspected were `HasFiniteCoalitionSupportPeeling`
in `MathUE/FiniteCoalitionSupportPeelingOrder.lean`,
`HasWeakQuittingPremiumSupportPeeling` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`,
and the original definitions of `quittingRootSuccessorPayoff`,
`quittingRootQuitPayoff`, and `quittingRootContinuePayoff` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
`Literature/README.md` and the header and clipped-map section of
`Literature/Simon2012.lean` were inspected for source separation; no
paper-derived theorem is assumed by this fixture or review.

Concrete next check: any standalone assembly should retain the distinction
between a selected returning root and universal return, and explicitly
include both premium-core replacement facts before transferring the proof.
