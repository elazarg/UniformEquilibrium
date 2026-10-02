# Candidate C and its entire nonsingleton fiber have a two-scale uniform payoff

**Identity:** `CODEX_NEGATIVE_CERTIFICATE`  
**Status:** proved in exact ordinary mathematics; the approximate-endpoint
extension of the checked singleton-mesh compiler is not yet instantiated in
Lean  
**Conjecture impact:** excludes the strongest explicit survivor in
`CODEX_RIEMANN__PERSISTENT_PAIR_CHAMBER_NO_GO.md`, together with all 44 reward
coordinates outside its four singleton rows, from the Fin4 counterexample
search

## Question

Candidate C survives the exact persistent-base and ordered two-date threat
screens and has a positive pure-toggle floor.  Does it remain a plausible
positive terminal-gap table once unrestricted periodic and late-clock
deviations are included?

The answer is **no**.  Its first two singleton rows admit a two-block cycle
whose terminal exploitability and payoff mismatch both tend to zero.  Mesh
subdivision makes every nonsingleton collision reward negligible.  Hence the
argument uses no nonsingleton coordinate at all except through the finite
reward bound.

## Data and quantifiers

Let the players be `0,1,2,3`.  Assume only the following singleton rewards:

```text
A = r({0}) = (1, -3/4,  0,  1/2),
B = r({1}) = (1, -1/2,  0, -1/4),
    r({2}) = (0,  1,   -1,  0),
    r({3}) = (1/4,1/2, 1/4,-1/4).
```

All 44 coordinates belonging to coalitions of cardinality at least two are
arbitrary.  Put

```text
M = max_{nonempty S,i} |r_i(S)|,
D = 2M.
```

The claim is against every randomized history-dependent unilateral behavioral
deviation, including Never and arbitrarily late stopping.  It is not a
bounded-controller assertion.

The target payoff is

```text
B = (1,-1/2,0,-1/4).
```

## Exact coarse cycle

Fix rational `0 < delta < 1`.  Use two singleton-owner blocks:

```text
owner 0 with total block hazard p0 = delta,
owner 1 with total block hazard p1 = 1/2.
```

The unique cyclic Bellman values `x` at the owner-0 block and `y` at the
owner-1 block solve

```text
x = delta A + (1-delta)y,
y = (1/2)B + (1/2)x.
```

Writing `d=1+delta`, exact solution gives

```text
x = (2 delta A + (1-delta)B)/d,
y = (B + delta A)/d.
```

Coordinatewise,

```text
x = (1,
     -1/2 - delta/(2d),
      0,
     -1/4 + 3delta/(2d)),

y = (1,
     -1/2 - delta/(4d),
      0,
     -1/4 + 3delta/(4d)).
```

Thus `y` approaches `B`, with the exact sup-norm bound

```text
||y-B||_infinity = 3delta/(4d) < 3delta/4.
```

The only failure of the exact balanced-cycle inequalities is player 1's solo
floor.  At every coarse vertex it fails by at most

```text
eta_delta = delta/(2d) < delta/2.
```

Every other player's own singleton payoff is weakly below both `x` and `y`.
Owner 0 is exactly active because `x_0=A_0=1`.  In owner 1's block all
interpolated player-1 values are at most `B_1=-1/2`; consequently continuing
is weakly worse than the prescribed mixture, rather than a profitable defect.

## Subdivision and the all-behavior estimate

Subdivide each coarse block into `m>0` equal-survival microphases, exactly as
in `quittingSingletonArcCycleRoot`.  If a block has total hazard `p`, its
micro-hazard is

```text
h_m(p) = 1 - (1-p)^(1/m).
```

Let

```text
hmax(delta,m) = max(h_m(delta), h_m(1/2)).
```

The rpow interpolants remain between their two endpoints.  Therefore every
microphase value is at least the relevant own singleton payoff minus
`eta_delta`.

At a microphase owned by `j`, a different player `i` who Quits obtains

```text
(1-h) r_i({i}) + h r_i({i,j}).
```

Since both rewards have absolute value at most `M`, its excess over the
current value is at most

```text
eta_delta + D h <= eta_delta + D hmax(delta,m).
```

For the active owner, pure Quit has the same bound.  Pure Continue is exact
for every passive player and for owner 0.  For owner 1 it is weakly below the
current value, by the last observation in the preceding section.  Hence, with

```text
e(delta,m) = eta_delta + D hmax(delta,m),
```

`value+e(delta,m)` is a Bellman supersolution for each selected player's
unilateral stopping problem.

The terminal seam is strict.  Player 0 faces the positive owner-1 hazard
`1/2`; player 1 faces the positive owner-0 hazard `delta`; players 2 and 3 face
both.  Thus every deleted-player opponent-survival product is below one.  The
same Snell comparison used by

```text
quittingCyclicHazardTerminalValue_le_add_of_quitError_exactContinue
```

then yields, for every behavioral replacement `tau_i`,

```text
U_i(profile(delta,m)[i <- tau_i])
  <= U_i(profile(delta,m)) + e(delta,m).
```

The checked theorem has exact prescribed-Continue as an interface premise.
Here one Continue inequality is strict in the favorable direction; inspection
of its supersolution proof shows equality is used only to establish the
corresponding `<=` Bellman branch.  The preceding calculation supplies that
branch directly.  This note therefore records an ordinary proof, not a claim
that the approximate-endpoint wrapper is already a named Lean declaration.

For each fixed `delta`, `hmax(delta,m)` tends to zero as `m` tends to infinity.
Now first choose `delta` small and then `m` large.  Both

```text
e(delta,m) -> 0,
||y-B||_infinity -> 0.
```

Terminal-to-uniform transfer gives profiles valid at every sufficiently long
horizon, and the triangle inequality changes delivery from the exact terminal
value `y` to the fixed target `B`.  Therefore `B` is a uniform-equilibrium
payoff for every finite reward table with the four displayed singleton rows.

## Boundary, stationary, periodic, and late-clock audit

Candidate C already came with the following exact screens:

* every pure stationary boundary root has exploitability at least `1/4`;
* every prescribed two- or three-player persistent-base Nash face is rejected;
* every ordered two-date threat chamber in the cited note is rejected; and
* an exact eight-date profile has unrestricted exploitability
  `3069083213250743827/10^20`.

The present two-scale construction explains why those screens do not produce
a gap.  It is periodic for fixed `(delta,m)`, covers Never and every late clock
by strict deleted-player contraction, and drives its all-behavior terminal
debt to zero.  Its parameters are chosen analytically; no raw search score or
bounded controller class is optimized.

## Sources and named declarations inspected

The exact Candidate C rows and its prior screens are in
`experiments/codex_riemann_inert_perturbation_search.py` and
`notes/CODEX_RIEMANN__PERSISTENT_PAIR_CHAMBER_NO_GO.md`.

The checked constructions and semantic consumers inspected were:

* `quittingSingletonArcCycleRoot`,
  `quittingSingletonArcCycleValue`, and
  `quittingSingletonArcCycle_phase_certificate` in
  `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`;
* `BalancedSingletonCycleCertificate` and its terminal/uniform compilers in
  `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`;
* `quittingCyclicHazardTerminalValue_le_add_of_quitError_exactContinue` and
  `isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue`
  in `UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`; and
* `quittingGame_isUniformεEquilibrium_of_terminalNash`, as used by the checked
  singleton-cycle uniform compiler.

## Proved and unproved

Proved here:

* Candidate C has no positive terminal exploitability gap;
* the fixed target `B` is a uniform-equilibrium payoff;
* the proof covers unrestricted behavioral deviations and arbitrary late
  clocks; and
* the result holds for the entire 44-coordinate nonsingleton fiber.

Not proved here:

* the full Fin4 conjecture;
* a general approximate-endpoint Lean certificate;
* completeness of the two-scale singleton construction; or
* anything about tables with different singleton rows.

## Next exact candidate family

The next candidate family should not retain a singleton matrix already
admitting either an exact balanced singleton cycle or the limiting two-block
pattern above.  A principled next seed is a rational singleton matrix with a
checked obstruction to every relabelled cyclic open-sign skeleton, such as
the `fullCoreMatrix` witness in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportLCPSignBarrier.lean`.
Nonsingleton coordinates should then be chosen subject to exact rejection of
pure boundary roots, stationary active faces, persistent bases, ordered
two-date threats, complementary-pair cycles, and late-clock limits.  Passing
those finite screens would still make a table only a candidate: an exact
positive-gap certificate must cover every behavioral profile.
