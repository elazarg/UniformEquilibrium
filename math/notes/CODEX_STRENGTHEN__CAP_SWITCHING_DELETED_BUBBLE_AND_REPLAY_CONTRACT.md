# Cap switching localizes to a pair-deleted bubble; Zeno needs a replay contract

Identity: `CODEX_STRENGTHEN`  
Date: 2026-08-31  
Status: ordinary mathematics, not checked in Lean. The finite-cube and
pure-time-switch ingredients are already checked separately. The new
paper-level points are the deleted-survival estimate in Theorem 4.1 and the
full-chord descaling theorem in Section 7. The specified full endpoint can be
fed into the checked paid-cap trichotomy, but that generic construction
forgets reset-cube/original-source ancestry and is already available at every
actual profile under a terminal exploitability gap. The new content is the
curvature-selected row together with its moving-tail/deleted-survival packet,
and the exact finite-splice no-go. No Fin4 chamber consumer, uniform
equilibrium, or export is claimed.

## 1. Question and answer

This note answers the three questions isolated in
[`CODEX_ROOT__CAP_SWITCHING_AND_TRACE_FRICTION_REVIEW.md`](CODEX_ROOT__CAP_SWITCHING_AND_TRACE_FRICTION_REVIEW.md)
and records the subsequent finite-splice comparison.

1. The finite Boolean-cube localization is exact. For a cube on `m`
   coordinates, the macro-minus-star remainder is the sum of exactly
   `binom(m,2)` contextual squares. On a stopping-law reset cube whose
   effective reset amplitudes are at most `C lambda`, every prescribed-payoff
   square and every fixed pure-time payoff square is at most
   `4 M C^2 lambda^2`.
2. Persistent first-order debt or cap curvature therefore gives two
   competing pure stopping times. After a subsequence, their first
   disagreement is either at one fixed finite date or escapes to infinity.
   In the escaping arm the ordinary paid-row estimate gives only
   `Omega(lambda)` full opponent reach. However, the *rectangle* and the
   stopping-law mixture structure give more: after deleting one of the two
   reset movers, the remaining opponents have a fixed positive survival
   floor at the original common source. In Fin4 this is a source-attached
   **pair-deleted bubble**. This is the strongest unconditional bubble output
   proved here; it is not a full-reach or terminal-law atom.
3. Zeno amplification is valid only for a replay object whose repeated
   survival and complete unrestricted-deviation seam are already
   compositional. A static paid cap charge is not an absorption charge. For a
   uniform-payoff decoder, contraction of joint survival alone is also
   insufficient: every player-deleted survival relevant to a unilateral cap
   must contract.
4. Descaling one of the two literal reset edges produces a full-chord
   endpoint with a fixed paid gain. A positive global minimum lets that
   endpoint instantiate the checked generic paid-cap trichotomy, but the
   trichotomy does not retain its cube ancestry. The same rectangle forces a
   macroscopic moving post-mark tail product, but not positive `Never` mass.
   Section 7 gives an exact all-proper Fin4 regression and shows that finite
   radial iteration cannot create the missing cemetery atom.

The first-stage missing live step is:

```text
source-attached pair-deleted bubble from an escaping cap switch
    != replayable chronological block
    != contraction of every player-deleted survival.
```

After Section 7, the strategically sharper residual is the absence of an
ancestry-preserving consumer joining the fixed-gain endpoint to its
source-attached survival packet; the generic paid-cap diagnostic may still
end in its already-known inert arm. See (7.19).

## 2. Exact finite Boolean-cube localization

Let `E={e_1,...,e_m}` be an ordered finite set and let

```text
F : P(E) -> R.
```

Write `A_j={e_1,...,e_j}`, with `A_0=empty`, and define the contextual square

```text
Sq(F;A;e,f)
  = F(A+e+f)-F(A+e)-F(A+f)+F(A).
```

### Theorem 2.1 (exact triangular localization)

One has the exact identity

```text
F(E)-F(empty)
  - sum_k [F({e_k})-F(empty)]
 = sum_{1 <= j < k <= m} Sq(F;A_{j-1};e_j,e_k).       (2.1)
```

In particular there are exactly

```text
N_E = binom(m,2)                                     (2.2)
```

summands. If the absolute value of the left side is at least `rho`, one
contextual square has absolute value at least `rho/N_E`.
For `m<2`, the remainder in (2.1) is identically zero and the localization
assertion is vacuous.

**Proof.** Telescope the full endpoint along the chosen order:

```text
F(E)-F(empty)
 = sum_k [F(A_k)-F(A_{k-1})].
```

For fixed `k`, subtract the empty-background `e_k` edge and move its
background successively through `e_1,...,e_{k-1}`:

```text
[F(A_k)-F(A_{k-1})]-[F({e_k})-F(empty)]
 = sum_{j<k} Sq(F;A_{j-1};e_j,e_k).
```

Summing over `k` proves (2.1). The last assertion is the triangle
inequality. `QED`

This is the ordinary-math form of the checked declaration
`QuittingStoppingLawResetCubeData.endpoint_sub_source_sub_frozen_eq_squareCurvatureSum`
in `TerminalSemanticStoppingLawResetCube.lean`. The checked dichotomy
`nearFrozenReturn_or_signedSquareAbove` is its threshold form.

### Vector and Fin4 constant

For `p` scalar coordinates `F_i`, let `R_i` denote the left side of (2.1).
If

```text
|sum_i R_i| >= rho,
```

then one coordinate and one contextual square satisfy

```text
|Sq(F_i;A;e,f)| >= rho/(p N_E).                       (2.3)
```

For Fin4, `p=4`, `m<=4`, and `N_E<=6`, so the loss is at most `24`. If only
the full macro has size at least `kappa lambda` and the frozen star is
`o(lambda)`, then eventually the remainder has size at least
`(kappa/2)lambda`, giving a debt square of size at least

```text
(kappa/48) lambda.                                   (2.4)
```

No semantic return follows from (2.1): it is only an identity for the chosen
observable.

## 3. Multi-affine `O(lambda^2)` remainder and cap switching

Fix a quitting reward table with absolute rewards at most `M`. At one common
source, replace coordinate `e` by a complete stopping-law chord of effective
amplitude `alpha_e`. Assume

```text
0 <= alpha_e <= C lambda.                             (3.1)
```

The targets and the source may depend on the index `n`; only `M`, the finite
cube size, and `C` are uniform.

### Proposition 3.1 (sharp square bound)

For every observer `i`, background face `A`, and fresh distinct `e,f`,

```text
|Sq(U_i;A;e,f)| <= 4 M alpha_e alpha_f
                  <= 4 M C^2 lambda^2.               (3.2)
```

The same estimate holds uniformly for the payoff of every fixed pure-time
deviation of `i`. If `i=e` or `i=f`, the latter square is actually zero,
because installing the deviation overwrites that coordinate.

**Proof.** Terminal payoff is separately affine in every complete stopping
law. The square is therefore exactly `alpha_e alpha_f` times the four-corner
rectangle at the full targets. Each corner lies in `[-M,M]`, so the rectangle
has absolute value at most `4M`. The same proof applies after first replacing
the observer by a fixed pure-time strategy. `QED`

The exact formulas and constants are already checked as

- `quittingTerminalPayoff_resetCube_square_eq_scale_mul_scale_mul`;
- `abs_quittingTerminalPayoff_resetCube_square_le`;
- `quittingPureTimeDeviationPayoff_resetCube_square_eq`; and
- `abs_quittingPureTimeDeviationPayoff_resetCube_square_le`

in `TerminalSemanticStoppingLawResetCube.lean`. For the nested radial cube,
the outer weight times the inner frontier scale is the effective amplitude;
`abs_frozenRadialFacePayoff_square_le` in `Frozen/RadialResetCube.lean`
already packages the bound as `4 M lambda^2`.

Let `B_i` be the unrestricted behavioral cap and `d_i=B_i-U_i`. From (3.2),

```text
|Sq(B_i)| >= |Sq(d_i)|-4 M C^2 lambda^2.              (3.3)
```

Thus any persistent first-order debt square is a persistent first-order cap
square. A first-order debt square cannot use the observer as either reset
mover: the cap is invariant under the observer's prescribed coordinate, and
then the debt square is just the negative prescribed-payoff square, hence
`O(lambda^2)`.

### Proposition 3.2 (asymptotically sharp two-response extraction)

Suppose along one fixed face, observer, and two off-diagonal movers,

```text
liminf |Sq(B_i)|/lambda >= kappa > 0,                 (3.4)
```

and every fixed pure-time square is `o(lambda)` uniformly over the pure-time
menu. For every `0<gamma<kappa`, after discarding finitely many indices there
are two pure times `q_n^-`, `q_n^+` and one of the two fixed square diagonals,
called `S_n -> R_n`, such that

```text
B_i(S_n)-eta_n <= V_{S_n}(q_n^-),
B_i(R_n)-eta_n <= V_{R_n}(q_n^+),

gamma lambda_n + eta_n
  <= V_{R_n}(q_n^+)-V_{R_n}(q_n^-),

V_{S_n}(q_n^+)-V_{S_n}(q_n^-) <= eta_n,

gamma lambda_n
  <= [V_{R_n}(q_n^+)-V_{R_n}(q_n^-)]
       -[V_{S_n}(q_n^+)-V_{S_n}(q_n^-)],             (3.5)
```

where `eta_n>0` and `eta_n=o(lambda_n)`. No cap attainment is assumed.

**Proof.** Take, for example, `eta_n=lambda_n^2` after passing to
`lambda_n<=1`. The uniform fixed-witness square budget and `3 eta_n` are
`o(lambda_n)`, while the gap between `gamma` and `kappa` is fixed. Apply the
four-corner supremum-switch lemma to the absolute cap curvature and pass to a
subsequence fixing which diagonal occurs. `QED`

This proposition is already available, at finite scale and with all
inequalities retained, through
`exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature` in
`TerminalSemanticPositiveSlopeRectangle.lean`. The direct debt adapter is
`exists_pureTimeWitnessSwitchCertificate_of_abs_debtCurvature`; the literal
reset-square edge wrapper is
`exists_resetCubePureTimeSquareEdgeWitnessSwitch_of_abs_debtCurvature`.

The two times in (3.5) are distinct. The checked constructor
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` turns their
receiving edge into a literal paid first-disagreement row of gain at least
`gamma lambda_n`. If `r_n` is their first disagreement and `L_n` the
opponents' survival to `r_n` at `R_n`, then

```text
gamma lambda_n <= 2 M L_n.                            (3.6)
```

This only gives `L_n=Omega(lambda_n)`. The next section uses the rectangle,
not merely the receiving edge, to get a scale-free deleted-survival floor.

## 4. Rectangle friction forces a source-attached pair-deleted bubble

For a profile `P` and two pure times `q^-`, `q^+` with first disagreement
`r`, put

```text
G(P)=V_P(q^+)-V_P(q^-).                               (4.1)
```

The two observer plans act identically before `r`. Hence, pointwise in all
opponent stopping times, their payoff difference vanishes whenever any
opponent Quits before `r`.

For a reset mover `e != i`, write

```text
H_{-i,-e}(P,r)
```

for the probability that every player other than `i` and `e` survives to
`r` at `P`. In Fin4 this is a two-player, or pair-deleted, survival.

### Theorem 4.1 (one-edge trace-friction estimate)

Suppose `P'` differs from `P` only by replacing mover `e`'s complete
stopping law by the mixture

```text
(1-alpha) mu_e + alpha nu_e.
```

Then

```text
|G(P')-G(P)| <= 4 M alpha H_{-i,-e}(P,r).             (4.2)
```

The same bound holds with any common law for the non-`e` players; in
particular it applies in either orientation of a literal reset-cube edge.
Indeed, the event defining `H_{-i,-e}` omits the changed mover `e`, so its
probability is exactly identical at the two edge endpoints.

**Proof.** Condition on all non-`e` opponent clocks. Affinity of the complete
stopping-law mixture extracts the factor `alpha`. If one of those opponents
Quits before `r`, both observer plans have taken the same actions and already
receive the same terminal payoff, so both full-target/source gap integrands
are zero. On the remaining event each gap lies in `[-2M,2M]`; their difference
is at most `4M`. Integrating proves (4.2). `QED`

This estimate is sharper than the unconditional `4M alpha` total-variation
bound precisely when the mover-deleted survival is small.

### Corollary 4.2 (persistent cap rectangle gives a deleted host)

Apply Theorem 4.1 along the two reset edges joining the diagonal profiles
`S_n` and `R_n` in (3.5). If both effective amplitudes are at most
`C lambda_n`, then

```text
gamma lambda_n
 <= 4 M C lambda_n [H_n^e+H_n^f].                    (4.3)
```

Consequently one of the two movers and one of the two edge contexts has

```text
H_n^h >= gamma/(8 M C).                               (4.4)
```

After a finite subsequence, the mover `h` and context are fixed.

All faces of the cube are made from the same source by `O(lambda_n)` complete
stopping-law mixtures. The event in (4.4) omits `h`, so changing all remaining
face coordinates back to the empty-face source changes its probability by
at most

```text
|E| C lambda_n.
```

Thus, eventually, the original common source satisfies

```text
H_{-i,-h}(source_n,r_n) >= gamma/(16 M C).             (4.5)
```

No survival probability is divided by in this argument. The displayed
constant uses only `M>0` and `C>0`, which are automatic after discarding
irrelevant zero-bound/zero-amplitude cases when a positive rectangle exists.

### Bounded-date versus escaping-date conclusion

Every sequence `r_n in Nat` has a subsequence of exactly one of the following
forms.

1. `r_n=r` is fixed. Then (3.5) is an order-`lambda_n` paid strategic row at
   a fixed finite depth, and (4.5) gives a fixed pair-deleted reach at that
   depth.
2. `r_n -> infinity`. Then (4.5) is a source-attached escaping
   pair-deleted bubble.

For the second statement, put the stopping-time laws of the players in
`I\{i,h}` on the compact one-point space `Nat union {infinity}` and take a
weakly convergent subsequence of their source product laws. For every fixed
`N`, eventually `r_n>N`, so the limiting law assigns at least
`gamma/(16MC)` to the event that all these players stop after `N`. Letting
`N` increase gives

```text
Pr(all players in I\{i,h} choose Never)
  >= gamma/(16 M C).                                  (4.6)
```

In Fin4, (4.6) is a positive **pair-Never atom in the pair-deleted limit**.
It is not necessarily an atom of the full terminal outcome law: the deleted
mover `h` may absorb before the mark. It also does not give a lower bound on
the paid row's full opponent reach `L_n` beyond (3.6).

### Sharp boundary of the conclusion

The supremum-envelope geometry alone cannot bound the stopping dates. On the
two-label menu `{n,Never}`, define

```text
f00(n)=f00(Never)=0,
f10(n)=lambda,   f10(Never)=0,
f01(n)=0,        f01(Never)=lambda,
f11(n)=f11(Never)=lambda,
```

and give every other label the same low payoff at all four corners. Every
fixed-label square is exactly zero, but the supremum square is `-lambda`.
The optimizers switch between time `n` and `Never`, whose first disagreement
escapes. This is an exact abstract envelope regression, not a claimed
quitting-table realization.

Likewise, a paid row alone cannot improve (3.6). In a Fin4 profile with two
inert players, let one opponent Quit at date zero with probability
`1-lambda` and Never with probability `lambda`; let the observer earn `1`
from Quitting alone at date `n` and `0` from Never. The time-`n` versus Never
edge is exactly `lambda`, and its opponent survival to `n` is exactly
`lambda`. This is a realizable sharpness example for the paid-row decoder,
not a counterexample to the stronger square-specific Theorem 4.1.

The relevant prior boundary is
[`CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION.md`](CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION.md),
which distinguishes deleted opponent reach from full actual reach for a
fixed-gain row. Corollary 4.2 is different: it uses the reset rectangle to
select one additional deleted mover and transfers a fixed survival floor
back to the common source.

## 5. Minimal replayable-block interface for Zeno amplification

The scalar calculation is useful only after the word "replayable" has been
typed. The logically minimal all-repeat interface at scale `n` is the
following.

### Replay data

For every integer `k>=0` there is an executable chronological object
`Repeat_n(k)` with the same entry port and retained source ancestry, together
with numbers

```text
0<a_n<=1,  e_n>=0,
Surv_n(k), Err_n(k)>=0,
```

such that:

1. **complete survival contraction**

   ```text
   Surv_n(k) <= (1-a_n)^k;                            (5.1)
   ```

   `Surv` dominates every terminal boundary coefficient needed by the
   decoder. For unrestricted behavioral deviations in a quitting game this
   normally means the maximum of the joint and **every player-deleted**
   survival, not joint survival alone;
2. **complete seam subadditivity**

   ```text
   Err_n(k) <= k e_n;                                 (5.2)
   ```

   `Err` dominates prescribed-payoff, Bellman/root-Nash, unrestricted-cap,
   terminal-law, and ancestry/passport errors required by the intended
   decoder, uniformly over arbitrary behavioral deviations;
3. **decoder closure:** whenever `Surv_n(k_n)->0` and
   `Err_n(k_n)->0`, the corresponding repeated objects are accepted by the
   stated terminal/uniform-payoff compiler with the selected common payoff.

These three displayed fields are proof-theoretically minimal. A usable
one-block structure can derive them from stronger local data:

- conditional on survival, the output port is literally the input port;
- the same strategy/cap/law/passport state is restored, not merely a nearby
  compact state;
- every required deleted survival contracts by at least `a_n` per copy;
- the one-copy seam estimate is uniform over every admissible continuation
  and unrestricted behavioral deviation; and
- concatenation preserves the marked ancestry and the decoder's payoff
  selection.

### Theorem 5.1 (typed Zeno amplification)

Assume the replay data above and

```text
e_n/a_n -> 0.                                        (5.3)
```

Then there are integers `m_n` such that

```text
Surv_n(m_n) -> 0,
Err_n(m_n) -> 0.                                     (5.4)
```

If `e_n>0`, put `r_n=e_n/a_n` and

```text
m_n=floor(1/(a_n sqrt(r_n))).                         (5.5)
```

After discarding finitely many terms,

```text
m_n a_n >= 1/sqrt(r_n)-a_n -> infinity,
m_n e_n <= sqrt(r_n) -> 0.                           (5.6)
```

Therefore

```text
Surv_n(m_n) <= exp(-m_n a_n) -> 0,
Err_n(m_n) <= m_n e_n -> 0.
```

On indices with `e_n=0`, take for example
`m_n=ceil(n/a_n)`. `QED`

### Three necessary warnings

1. **Paid charge is not survival charge.** The `Omega(lambda)` gain in
   (3.5) is a payoff/cap rectangle. Nothing above turns it into the `a_n` in
   (5.1). A chronological absorption or deleted-survival conversion is an
   additional theorem.
2. **Joint survival is not enough.** A block in which only player `p` has
   hazard can have joint survival `(1-a)^k`, while the `p`-deleted survival is
   identically one. Player `p`'s unrestricted continuation cap still sees
   the terminal boundary with full weight.
3. **One-use recurrence is not replayability.** A two-port block can absorb
   with probability `a` on its first use and, on survival, move to a port at
   which all later copies survive surely. Its one-block data have `e=0` and
   positive `a`, but repeated survival remains `1-a`. Exact restart or the
   direct all-repeat estimate (5.1) is indispensable.

Thus compact recurrence, a repeated finite label, or an `o(lambda)` static
reset remainder does not by itself license (5.5).

## 6. What is checked, what is new, and what remains

### Checked declarations inspected

- `quittingStoppingLawMixtureBehaviorStrategy`,
  `quittingBehaviorStoppingLaw_stoppingLawMixture`, and
  `quittingTerminalPayoff_update_stoppingLawMixture_eq` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`;
- `QuittingStoppingLawResetCubeData`,
  `endpoint_sub_source_sub_frozen_eq_squareCurvatureSum`, the exact terminal
  and pure-time square scaling formulas, and their `4M` bounds in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`;
- `exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature` and its
  debt version in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
- `exists_resetCubePureTimeSquareEdgeWitnessSwitch_of_abs_debtCurvature` in
  `TerminalSemanticStoppingLawResetCubeOrientation.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `TerminalSemanticPaidFirstDisagreement.lean`;
- `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` in
  `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`;
- `frozenRadialFacePayoff_square_eq_weights_mul_innerSquare`,
  `abs_frozenRadialFacePayoff_square_le`, and the radial cap nonadditivity
  localization in `UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialResetCube.lean`;
- `exists_frozenRadialPaidSquare_of_negativeSquare` and
  `exists_fixed_frozenRadialStrategicLabel_of_scaleNormalizedLiminfLower` in
  `Frozen/RadialCurvatureStrategicDispatch.lean`.

The last declaration explicitly allows the first-disagreement dates to
diverge; it packages their paid legal gain but not Corollary 4.2's transfer
to a common-source pair-deleted bubble.

### Paper-level new targets

Theorem 4.1 and Corollary 4.2 are one narrow formalization target:

```text
first-order source-matched stopping-law cap rectangle
  -> fixed finite paid row
     or escaping common-source pair-deleted Never bubble.
```

They are supplied-object consequences. They do not show that an arbitrary Fin4
positive-minimum hard source has persistent curvature, nor do they consume
the pair-deleted bubble into a terminal equilibrium.

Section 7 adds the full-chord descaling adapter and the exact all-proper
regression. Those statements use the same checked affine-payoff and paid-row
interfaces, but are ordinary mathematics here.

### Intermediate boundary, refined in Section 7

At this stage the open question was whether the source-attached bubble,
retained reset mover, and positive-minimum passport produced a chronological
contraction or renewable rank. Section 7 settles the direct finite-splice
attempt negatively: even an exact first-order Fin4 cap switch can remain in
the all-proper, cap-tight splice class. It also extracts a stronger specified
full-endpoint paid row, while showing that the checked generic paid-cap port
forgets the ancestry needed to combine that row with the bubble. Thus this
subsection is historical motivation, not a current obligation.

## 7. Full-chord descaling, finite-splice mismatch, and an all-proper regression

This section continues the comparison requested after the first draft. The
finite-splice obstruction in
[`CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY.md`](CODEX_EULER__POSITIVE_MINIMUM_FINITE_SPLICE_INERT_BOUNDARY.md)
is, for a moved law `mu_h`,

```text
NeverMass(mu_h)
  * MaxPairDeletedSurvivalLimit(profile,h).           (7.1)
```

Corollary 4.2 controls a pair-deleted survival at the *moving finite date*
`r_n`; neither factor in (7.1) is continuous under such an escaping clock.
There is nevertheless a stronger endpoint consequence of the rectangle.

### 7.1 Full-chord descaling theorem

Consider the diagonal `S_n -> R_n` and witnesses from (3.5). Join the two
diagonal vertices by two literal reset edges and put

```text
G_n(P)=V_P(q_n^+)-V_P(q_n^-).
```

The rectangle inequality says

```text
gamma lambda_n <= G_n(R_n)-G_n(S_n).                 (7.2)
```

Hence one of the two edges, belonging to a mover `h`, has

```text
|G_n(P_n')-G_n(P_n)| >= gamma lambda_n/2.            (7.3)
```

Suppose the effective law on that inserted edge is

```text
mu_{h,n}'=(1-alpha_{h,n})mu_{h,n}+alpha_{h,n}nu_{h,n},
0<alpha_{h,n}<=C lambda_n.                           (7.4)
```

All other laws are fixed along the edge. Separate affinity of each fixed
pure-time payoff gives the exact identity

```text
G_n(P_n')-G_n(P_n)
 = alpha_{h,n}[G_n(P_n[h<-nu_{h,n}])-G_n(P_n)].       (7.5)
```

Combining (7.3)--(7.5),

```text
|G_n(P_n[h<-nu_{h,n}])-G_n(P_n)| >= gamma/(2C).      (7.6)
```

Therefore one of the two actual full-chord endpoints, denoted `E_n`, has

```text
|G_n(E_n)| >= gamma/(4C).                            (7.7)
```

Reverse the order of the two witnesses if necessary. The checked
first-disagreement constructor then gives on `E_n` a literal paid row of
fixed gain

```text
g = gamma/(4C)>0.                                    (7.8)
```

This uses no division by a survival probability and no cap attainment. It is
an exact ordinary-math consequence of the complete stopping-law mixture,
not merely a compact limit statement.

For the nested radial cube, `nu_{h,n}` is the original frontier replacement:
the outer radial weight and the inner frontier mixture compose to the
effective coefficient `alpha_{h,n}=weight_h lambda_n`. Thus `E_n` is an
actual profile with at most one full frontier replacement and the other
coordinates at literal radial-face laws.

The endpoint row instantiates an existing generic diagnostic. Given the
positive global semantic minimum, use `E_n`, its observer, (7.8), and its row
as the fields of `QuittingPaidCapLiftedSource`. Then
`QuittingPaidCapLiftedSource.nonempty_summablePort` and
`QuittingPaidCapLiftedSource.exactTrichotomy` give

```text
charged admissible near-return
or quantitative debt descent
or literal inert stall.                              (7.9)
```

Under the maintained terminal exploitability gap the first arm yields a
uniform-equilibrium payoff and is excluded, leaving descent or inert stall.
This instantiation is the two-coordinate analogue of the one-ray
full-endpoint adapter in
`NormalizedCurvaturePaidRow.lean` and
[`CODEX_EULER__MINIMUM_MIDPOINT_OFFMIN_CURVATURE_PAID_PORT.md`](CODEX_EULER__MINIMUM_MIDPOINT_OFFMIN_CURVATURE_PAID_PORT.md).
No inspected declaration currently packages (7.2)--(7.8) for a reset square,
but the target source structure requires no additional field.

That last fact is also the exact scope loss. `QuittingPaidCapLiftedSource`
does not store the reset cube, the original common source, the full endpoint's
ancestry, or the pair-deleted packet. Its descent or inert output therefore
cannot be read as a child attached to the original cap-switch source.
Moreover, under a terminal exploitability gap,
`HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` already
constructs such a generic paid-cap port at every actual profile. Entry into
(7.9) is consequently not a new chamber consumer. The new statement is the
more structured conjunction:

```text
specified cap-curvature witnesses
  -> fixed-gain row at a specified source-built full endpoint
     + source-attached pair-deleted/post-mark packet.               (7.9a)
```

The generic trichotomy currently forgets the link between those two outputs.

### 7.2 What the rectangle forces about post-mark mass

Theorem 4.1 admits the sharper edge bound

```text
|G(P')-G(P)|
 <= 2 M alpha H_{-i,-h}(P,r)
      [mu_h([r,infinity])+nu_h([r,infinity])].        (7.10)
```

Indeed, after conditioning on the other opponents surviving to `r`, the
pure-time gap is zero whenever `h` stops before `r`, and otherwise has
absolute value at most `2M` under either endpoint law.

Selecting the edge in (7.3) gives

```text
H_{-i,-h}(P_n,r_n)
 [mu_{h,n}([r_n,infinity])+nu_{h,n}([r_n,infinity])]
 >= gamma/(4MC).                                     (7.11)
```

Hence one full-chord endpoint has a macroscopic product

```text
tailMass_h(r_n) * pairDeletedSurvival(r_n)
 >= gamma/(8MC).                                     (7.12)
```

Equivalently, its full opponent survival to the first disagreement is
macroscopic, consistent with the fixed-gain paid row in (7.8).

But (7.12) is a **moving post-mark tail** product, inclusive of the mark. In
the notation of the checked finite-splice file its exact decomposition is

```text
tailMass_h(r_n)
 = StopMass_h(r_n)+LateFiniteMass_h(r_n)+NeverMass_h. (7.13)
```

The other players in the pair-deleted factor may likewise stop surely at
finite dates at or after `r_n`. In particular the mover factor may be carried
entirely by an atom at the disagreement mark, which is already removed by a
finite splice whose cutoff is `r_n`. Consequently (7.12) does not imply
either

```text
NeverMass_h>0
```

or a positive terminal `MaxPairDeletedSurvivalLimit`. It therefore does not
imply (7.1). The generic paid-cap diagnostic (7.9) remains applicable to the
endpoint row, but it neither consumes this post-mark packet nor preserves its
source ancestry.

### 7.3 Exact Fin4 all-proper cap-switch regression

The failure above occurs in an actual quitting game, not only in an abstract
maximum of affine functions. This regression falsifies the local implication

```text
first-order stopping-law cap square
+ escaping pair-deleted bubble
  -> positive Never x terminal pair-deleted product. (7.14)
```

It is not claimed to have positive global minimum.

Take four players `i,a,b,c`; `i` is the cap observer and `a,b` are the reset
movers. For indices `n>=2`, put

```text
r_n=n,  lambda_n=1/n,  K_n=n^3,  delta_n=1/K_n,
L_n=2n.
```

At the common source:

- `a`'s stopping time is uniform on
  `{L_n,...,L_n+K_n-1}`;
- `b` stops surely at `L_n+K_n`;
- `c` stops surely at `L_n+K_n+1`;
- `i` may be prescribed Never (its prescribed law is irrelevant to its cap).

The full target of each mover `a,b` stops surely at `r_n`. Mix each complete
source law with its target at intensity `lambda_n`. Let `x,y` denote the
actual target weights of `a,b`, so the four cube corners have
`x,y in {0,lambda_n}`.

All rewards of `a,b,c` are zero. The observer's reward is one precisely on

```text
{i,a}, {i,a,b}, {b}, {a,b},
```

and zero on every other terminal coalition. Direct conditioning on the
stopping times gives the following complete pure-time menu.

- Quitting at `r_n` has value `x`.
- Quitting strictly between `r_n` and `L_n`, or choosing Never, has value
  `y`.
- Quitting at any date in `a`'s source window has value

  ```text
  y+(1-x)(1-y)delta_n.
  ```

- Every other pure time has value at most one of these values.

Behavioral pure-time extremality therefore gives the exact unrestricted cap

```text
B_i(x,y)=max{x, y+(1-x)(1-y)delta_n}.                 (7.15)
```

Since `delta_n<lambda_n`, its four corner values are

```text
B00=delta_n,
B10=lambda_n,
B01=lambda_n+(1-lambda_n)delta_n,
B11=lambda_n+(1-lambda_n)^2 delta_n.
```

Thus the cap square is

```text
B11-B10-B01+B00
 = -lambda_n+(1-lambda_n+lambda_n^2)delta_n,
```

and hence

```text
(cap square)/lambda_n -> -1.                         (7.16)
```

Every fixed pure-time square is zero except in `a`'s source window, where it
is exactly `delta_n lambda_n^2`; in particular the uniform fixed-witness
remainder is `o(lambda_n)`.

The two active cap responses are the finite time `r_n` and a date in the
moving late window. Their first disagreement escapes, and every opponent
survives to `r_n` with probability one at all full source/target endpoints.
Nevertheless:

```text
NeverMass(a)=NeverMass(b)=NeverMass(c)=0              (7.17)
```

at the source, targets, every cube face, and every full endpoint. In fact all
three laws have finite support. Hence the moved-law Never factor in (7.1) is
zero for both reset movers. Also every terminal pair-deleted survival limit
contains at least one of these zero-Never laws and is zero. The checked
classification
`tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern` therefore
places the example in the cap-tight finite-splice arm, despite (7.16) and the
escaping pair-deleted bubble.

The weak stopping-law limit sends the late finite source laws to Never, so
the pair-Never atom of (4.6) is present in the compact limit. Equation (7.17)
shows exactly why that compact atom is not the actual cemetery factor used by
the finite-splice theorem.

### 7.4 Finite radial/active-face iteration cannot repair the mismatch

Never mass is affine under complete stopping-law mixing:

```text
Never((1-alpha)mu+alpha nu)
 =(1-alpha)Never(mu)+alpha Never(nu).                (7.18)
```

Therefore the class of proper laws with zero Never mass is closed under:

- every literal Boolean reset face;
- every radial weighting of such a face;
- rebasing followed by another finite family of proper-law resets; and
- any finite, even index-dependent, number of active-face mixture steps.

The regression above remains inside this invariant class. Repeating the
radial mixture can increase the effective finite target weight, but it cannot
make (7.1) positive. Across `n`, an escaping sequence of proper laws can
converge weakly to Never; taking that weak limit is exactly the nonactual
compactification which the finite-splice cutoff can chase.

Thus no finite iterated radial-mixture or active-face argument forces the
missing cemetery atom. Such an argument would need a genuinely new input:

1. a source/target law already carrying positive Never mass;
2. a cutoff-uniform tail tightness theorem converting (7.12) to actual
   cemetery mass; or
3. an ancestry-preserving chronological consumer that keeps the fixed-gain
   full endpoint row (7.8) attached to its source packet.

The generic paid-cap trichotomy (7.9) is not item 3: it is universally
available under the terminal gap and forgets the source/cube provenance. Its
inert arm remains live. The revised residual is therefore not the raw cap
switch and not the finite-splice product. It is:

```text
curvature-selected fixed-gain full-chord endpoint
+ source-attached macroscopic moving post-mark packet
+ generic trichotomy forgets their ancestry link
+ possible literal inert stall.                     (7.19)
```

### 7.5 Additional checked interfaces inspected

The finite-splice comparison uses the exact definitions and limit statements

- `quittingFiniteSpliceError` and
  `tendsto_quittingFiniteSpliceError_terminal` in
  `TerminalSemanticStoppingLawFiniteSplice.lean`; and
- `quittingPairDeletedSurvivalLimit_eq_prod_neverMass`,
  `quittingMaxPairDeletedSurvivalLimit_eq_zero_iff_two_zeroNever`, and
  `tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern` in
  `TerminalSemanticStoppingLawFiniteCapClock.lean`.

The generic full-endpoint diagnostic uses the structure
`QuittingPaidCapLiftedSource` and theorem
`QuittingPaidCapLiftedSource.nonempty_summablePort` in
`Endpoint/PaidCapLiftedSummablePort.lean`, followed by
`QuittingPaidCapLiftedSource.exactTrichotomy` in
`Endpoint/PaidCapPortExactTrichotomy.lean`. The charged branch contains a
checked unrestricted uniform-equilibrium payoff. Under a positive terminal
exploitability gap it is excluded exactly as in
`QuittingActualProfileTerminalGapPaidCapPort.quantitativeDebtDescent_or_inertStall`
in `Endpoint/ActualProfileTerminalGapPaidCap.lean`.

None of those declarations asserts (7.10)--(7.12), the full-chord descaling
(7.5)--(7.8), or the all-proper regression. Those are the ordinary-math
contributions of this continuation.

### 7.6 Independent review disposition

The independent review
[`CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT__BY_CODEX_CURVATURE_REVIEW.md`](../feedback/CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT__BY_CODEX_CURVATURE_REVIEW.md)
passed Theorem 4.1, Corollary 4.2, full-chord descaling, all constants, and the
exact all-proper regression. It requested two scope clarifications, both now
incorporated:

1. the generic paid-cap trichotomy forgets reset-cube/original-source
   ancestry; and
2. terminal exploitability already supplies a paid-cap port at every actual
   profile, so trichotomy entry itself is not a new chamber consumer.

No mathematical objection remains from that review. A focused boundary
packet could extract Theorem 4.1, Corollary 4.2, (7.5)--(7.12), and the
all-proper regression. The conditional Zeno replay interface should not be
presented as part of that no-go result. A scope-faithful proposed packet title
is
[`CAP_SWITCH_RECTANGLE_FULL_CHORD_AND_FINITE_SPLICE_BOUNDARY.md`](../formalized/CAP_SWITCH_RECTANGLE_FULL_CHORD_AND_FINITE_SPLICE_BOUNDARY.md).
