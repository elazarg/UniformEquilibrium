# Global KKT source: an actual two-law competitor and its unresolved full cap

Author: `CODEX_NOETHER_SUPPORT`

## Status

Paused at the requested checkpoint. The formulas below are proved ordinary
mathematics, not Lean-checked. They compare a noninfinitesimal, actual
independent-law competitor with the global finite-clock minimum. They do
**not** consume the all-proper timing-bubble arm, exclude a positive limiting
minimum, or give a new uniform-equilibrium theorem.

The precise failed step is replacing the full response envelope by its two
KKT-selected gains. Both selected gains can be made small, and vanish at the
far corner, but global minimality can be maintained by a different response
of either changed player or by either unchanged player. The complete
after-menu tester is part of this unresolved envelope.

## Question and source input

Fix four players, a terminal reward table with absolute coordinates at most
M > 0, independent private stopping laws on Nat ∪ {Never}, and payoff zero
when nobody quits. Nothing below uses signs of singleton rewards. In
particular it applies to the canonical single-pivot normalization.

Write A_K = {0,…,K−1,Never}. A controller is an actual product law in
X_K = ∏ᵢ Δ(A_K). Its complete pure response menu is
Â_K = {0,…,K,Never}: every later finite response is outcome-equivalent to K.
For a profile P put

```text
gᵢ,ᵤ(P) = Vᵢ,ᵤ(P₋ᵢ) − Uᵢ(P),
E(P) = maxᵢ,ᵤ gᵢ,ᵤ(P),       η_K = min_{P ∈ X_K} E(P).
```

The cap equals the supremum over all complete behavioral deviations, not
only the controller menu. Suppose hypothetically η_K decreases to m > 0.

Take an actual global minimizer μ ∈ X_K and the internal cross-amplification
arm of the named KKT source. There are distinct players j,i, r ∈ A_K and
t ∈ Â_K such that, with η = η_K,

```text
gⱼ,ᵣ(μ) = gᵢ,ₜ(μ) = η,
b = gᵢ,ₜ(μ[j ← δᵣ]) − η ≥ η/3.
```

The main source also extracts a paid support time and an escaping-row
counterfactual timing bubble. This checkpoint does not reproduce that
extraction. Its attempted subclaim was: can simultaneous changes of the two
complete laws make the actual full exploitability less than m, using the
global-minimizer hypothesis and the displayed cross-amplification?

## The actual square

For 0 ≤ α,β ≤ 1 define

```text
P(α,β)ⱼ = (1−α) μⱼ + α δᵣ,
P(α,β)ᵢ = (1−β) μᵢ + β δₜ,
P(α,β)ₖ = μₖ                         (k distinct from i,j).
```

Each player performs their own private mixture. This is a product of mixed
laws, not a correlated mixture of two profiles. It changes entire laws and
does not require a lower bound on the mass of an extracted support atom.

Set L = K if t ∈ A_K and L = K+1 if t = K. Every P(α,β) belongs to X_L.
All its complete gains must therefore be evaluated for u ∈ Â_L. In the
second case this includes K+1. At the original corner, tests K and K+1 are
equivalent, but they need not remain equivalent after player i is placed at
K: another player can quit simultaneously with i at K or wait until K+1.

For each complete tester (k,u) define its four actual corner gains

```text
hᵏ,ᵤ_ab = gₖ,ᵤ(P(a,b)),                 a,b ∈ {0,1}.
```

Multiaffinity of terminal expectations gives the exact full-square identity

```text
gₖ,ᵤ(P(α,β))
 = (1−α)(1−β) hᵏ,ᵤ_00 + α(1−β) hᵏ,ᵤ_10
   + (1−α)β hᵏ,ᵤ_01 + αβ hᵏ,ᵤ_11.                 (1)
```

This is an identity for each gain, not for their maximum. Every corner is
an actual independent profile. A tester owned by one of the changed players
still obeys (1), since its deviation payoff simply does not depend on that
player's prescribed law.

## The two marked gains

Define the reverse cross increment

```text
a = gⱼ,ᵣ(μ[i ← δₜ]) − η.
```

The KKT input bounds b below, but supplies no favorable sign or product
bound for a. Affinity in one's own prescribed law gives

```text
gⱼ,ᵣ(P(α,β)) = (1−α)(η + βa),
gᵢ,ₜ(P(α,β)) = (1−β)(η + αb).                    (2)
```

In particular both gains vanish at P(1,1). More uniformly, every response
gain is at most 2M, so the factorization proves

```text
gⱼ,ᵣ(P(α,β)) ≤ 2M(1−α),
gᵢ,ₜ(P(α,β)) ≤ 2M(1−β).                         (3)
```

Consequently both marked gains are at most m/2 throughout the actual
noninfinitesimal corner square α,β ≥ 1−m/(4M). No limiting law,
infinitesimal variation, or atom-mass estimate is used here.

For completeness, the balancing path β = (b/η)α gives the exact expressions

```text
gᵢ,ₜ = η − (b²/η)α²,
gⱼ,ᵣ = η + (ab/η−η)α − (ab/η)α²,
```

where the path stays in the unit square. Even when these two expressions
decrease, they do not bound E. This calculation is not promoted to a
second-order cap-switch criterion.

## What global minimality actually supplies

For every point of the entire square,

```text
max_{k ∈ I, u ∈ Â_L} gₖ,ᵤ(P(α,β)) ≥ η_L ≥ m.    (4)
```

If L = K, the first lower bound is η. If L = K+1 it is η_{K+1}, not η;
the difference η_K−η_{K+1} tends to zero along growing horizons. Thus the
complete tester cannot be kept fixed by silently treating t = K as an
internal controller move.

Combining (3) and (4), throughout the corner square some **unmarked** tester
has gain at least m. At P(1,1) the alternatives can be stated exactly:

- a player outside {i,j} has gain at least m; or
- player j has a pure response u whose payoff exceeds that of r by at least
  m against the opponents with player i fixed at t; or
- player i has a pure response u whose payoff exceeds that of t by at least
  m against the opponents with player j fixed at r.

In the second alternative r was cap-attaining at μ. Hence the change in the
response-payoff difference Vⱼ,ᵤ−Vⱼ,ᵣ is at least m plus its original
nonnegative cap slack Vⱼ,ᵣ−Vⱼ,ᵤ. The analogous statement holds in the third
alternative. These are exact endpoint consequences, not a claim that such
switches are impossible. The unmarked tester can depend on α,β and K.

Equation (4) uses actual global minimum comparison, not merely KKT. But its
combination with the marked-gain identities does not give an upper bound
below m for the remaining terms in (1). The timing-bubble survival floor is
attached to selected counterfactual corners and a selected response
difference. It supplies no such bound on all those other complete gains.

Accordingly the implication

```text
two marked complete-response gains decrease
    ⇒ the full unrestricted exploitability decreases
```

is not established. No solved-table example has been substituted for a
hypothetical positive limiting minimum, and no table-class counterexample
is claimed. No compression of payoffs or date-forgetting terminal laws is
used: neither would preserve the full response caps required in (1)–(4).

## Sources inspected

The bounded reading consisted of the following main note and its named
KKT/response-square dependencies:

- [Finite-clock KKT fixed face or full timing bubble](CODEX_HAHN__FINITE_CLOCK_KKT_FIXED_FACE_OR_FULL_TIMING_BUBBLE.md).
- [Finite-clock exploitability KKT boundary or cross-amplification](CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION.md),
  especially its simultaneous multiplier theorem and internal arm.
- [KKT cross-amplification to pure-time paid row](CODEX_HAHN__KKT_CROSS_AMPLIFICATION_TO_PURE_TIME_PAID_ROW.md).
- [Cap-switch rectangle full chord and finite-splice boundary](../formalized/CAP_SWITCH_RECTANGLE_FULL_CHORD_AND_FINITE_SPLICE_BOUNDARY.md),
  for the distinction between selected response differences and full caps.

Named Lean declarations inspected in their source files, without running a
build or claiming a new Lean result:

- `exists_minimum_quittingControllerFiniteWordLoss`,
  `antitone_quittingControllerFiniteWordValue`, and
  `tendsto_quittingControllerFiniteWordValue` in
  `UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`.
- `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` in
  `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.

## Concrete restart question

At genuine positive-gap global minimizers in the all-proper escaping-row
arm, can source information force one point of this actual two-law square
to have **every** unmarked complete tester below m, including the after-menu
tester? The present calculation supplies no such control. Work stops here;
the all-proper timing-bubble arm remains unconsumed.
