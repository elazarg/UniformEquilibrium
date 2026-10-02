# Cap-switch rectangles produce full-chord paid rows but not finite-splice cemetery mass

Authors: `CODEX_STRENGTHEN`

Independent review:
[`CODEX_CURVATURE_REVIEW`](../feedback/CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT__BY_CODEX_CURVATURE_REVIEW.md)

Research record:
[`CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT.md`](../notes/CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT.md)

## Exact statement

Let `I` be a nonempty finite player set. A terminal quitting reward table
assigns a payoff vector to every nonempty quitting coalition. Fix an observer
`i in I` and a bound `M>0` such that every terminal reward coordinate has
absolute value at most `M`.

Every behavioral profile below is used through its complete stopping laws on

```text
Nbar = Nat union {Never}.
```

For an actual profile `P` and a pure stopping time `q in Nbar`, let `V_P(q)`
be player `i`'s expected terminal payoff after replacing only `i` by `q`.
Let

```text
B_i(P) = sup_q V_P(q).
```

This equals the supremum over all unilateral behavioral deviations of `i`.
For two pure times `q-` and `q+`, let `r` be their first disagreement date
and put

```text
G(P) = V_P(q+) - V_P(q-).
```

Thus the two deviations take identical actions strictly before `r`. For a
mover `h != i`, define the pair-deleted survival

```text
H_{-i,-h}(P,r)
 = Pr_P(T_k >= r for every k notin {i,h}).            (1)
```

Survival to `r` means no stop strictly before `r`; a stop at `r` is retained.

### Theorem A: one-edge deleted-survival friction

Suppose `P'` differs from `P` only in mover `h`'s law, changing it from
`mu` to

```text
(1-alpha) mu + alpha nu,    0 <= alpha <= 1.
```

Then

```text
|G(P')-G(P)| <= 4 M alpha H_{-i,-h}(P,r),             (2)
```

and, more sharply,

```text
|G(P')-G(P)|
 <= 2 M alpha H_{-i,-h}(P,r)
      [mu([r,Never]) + nu([r,Never])].                (3)
```

Here `[r,Never]` contains all finite dates at least `r` and the Never point.
The deleted survival in (1) is identical at the two edge endpoints because
the changed mover is omitted.

### Theorem B: a first-order reset rectangle

Let `lambda_n>0` tend to zero. Fix constants `C,gamma>0`. For every `n`, let
four actual profiles form one literal two-coordinate stopping-law reset
square inside a finite reset cube based on a common source `P_n^0`. Every
cube coordinate is changed by a complete-law mixture of effective amplitude
at most `C lambda_n`. Assume the two reset movers are distinct from `i`.

Suppose a cap-switch certificate selects two diagonal vertices `S_n,R_n`
and pure times `q_n^-,q_n^+` such that, after orienting the diagonal,

```text
gamma lambda_n
 <= [V_{R_n}(q_n^+) - V_{R_n}(q_n^-)]
      -[V_{S_n}(q_n^+) - V_{S_n}(q_n^-)].            (4)
```

Let `r_n` be the first disagreement of these pure times. If the whole cube
has at most `m` reset coordinates, then, after passing to a subsequence, one
fixed reset mover `h`, one literal edge context `P_n`, and its mixed endpoint
`P_n'` have all the following properties.

1. The selected literal edge carries half the rectangle:

   ```text
   |G_n(P_n')-G_n(P_n)| >= gamma lambda_n/2.          (5)
   ```

2. Its pair-deleted survival has a scale-free floor:

   ```text
   H_{-i,-h}(P_n,r_n) >= gamma/(8MC).                 (6)
   ```

3. Returning all face coordinates to the common source changes this event
   by at most `m C lambda_n`. Consequently, eventually,

   ```text
   H_{-i,-h}(P_n^0,r_n) >= gamma/(16MC).              (7)
   ```

4. Write the effective selected edge as

   ```text
   mu_n'=(1-alpha_n)mu_n+alpha_n nu_n,
   0<alpha_n<=C lambda_n.
   ```

   Let `P_n[h<-nu_n]` be its literal full-chord target. One of the two
   full-chord endpoints

   ```text
   E_n in {P_n, P_n[h<-nu_n]}
   ```

   has, after swapping `q_n^-` and `q_n^+` if necessary, a positive pure-time
   edge of fixed gain

   ```text
   V_{E_n}(q_n^+) - V_{E_n}(q_n^-) >= gamma/(4C).    (8)
   ```

   Hence `E_n` carries a literal paid first-disagreement row of gain
   `gamma/(4C)`.

5. The same endpoint can be chosen so that its full opponent survival to the
   disagreement mark is macroscopic:

   ```text
   Pr_{E_n}(T_k >= r_n for every opponent k != i)
     >= gamma/(8MC).                                 (9)
   ```

   Equivalently, for the selected endpoint law `rho_{h,n}`,

   ```text
   rho_{h,n}([r_n,Never])
     * H_{-i,-h}(P_n,r_n) >= gamma/(8MC).             (10)
   ```

After a further subsequence, either `r_n` is one fixed finite date or
`r_n -> infinity`. In the escaping case, every weak limit of a suitably
selected subsequence of the common-source laws of the players outside
`{i,h}` satisfies

```text
Pr(T_k=Never for every k notin {i,h})
  >= gamma/(16MC).                                   (11)
```

This is a pair-deleted Never atom in a weak limit. It is not an actual Never
atom of any profile in the sequence.

### Theorem C: exact all-proper Fin4 regression

There is one fixed four-player quitting reward table and a sequence of
literal two-coordinate reset squares satisfying:

```text
cap square / lambda_n -> -1,
sup over pure times |fixed-time square| = o(lambda_n),
r_n -> infinity,
full opponent survival to r_n = 1,
```

while every source, target, face, and full endpoint law of the three
opponents is proper, with Never mass zero. Therefore the exact terminal
finite-splice product

```text
NeverMass(moved law)
  * MaxPairDeletedSurvivalLimit(profile,mover)        (12)
```

is zero at every index. The universal finite-splice error is cap-tight and
can be sent to zero by finite cutoffs despite the first-order cap rectangle,
the fixed full-chord paid row, and the pair-deleted weak-limit atom.

Moreover, every finite iteration of Boolean-face or radial mixtures whose
inputs are proper laws remains proper. Thus finite active-face iteration
cannot manufacture the missing factor in (12).

## Conjecture-facing change

The positive-curvature arm of
[`FIN4_JENSEN_CLOCK_SELECTION_AND_CAP_LEAKAGE.md`](../questions/FIN4_JENSEN_CLOCK_SELECTION_AND_CAP_LEAKAGE.md)
asks for a source-preserving consumed response square or paid
first-disagreement charge. The cap-switching reduction had left open whether
an escaping first-disagreement row could be consumed by compactifying its
survival packet to a Never atom and then invoking the checked finite-splice
theorem.

Theorem C removes that route exactly:

```text
first-order cap rectangle
  -> escaping pair-deleted weak Never atom
  -/-> positive actual NeverMass * terminal pair-deleted survival
  -/-> finite-splice obstruction or consumer.        (13)
```

The failure occurs in one exact Fin4 quitting table, not merely for an
abstract supremum of affine functions. Theorems A and B give the strongest
replacement statement currently justified: the same curvature specifies a
fixed-gain paid row at a source-built full-chord endpoint and a macroscopic
source-attached post-mark packet.

The remaining obligation is consequently sharper. A curvature consumer must
preserve the common-source/reset-cube ancestry linking those two outputs, or
must add a genuinely new tightness/cemetery hypothesis. Passing the endpoint
through the generic paid-cap port does not do this: that construction forgets
the cube, common source, full-chord ancestry, and deleted-survival packet.
This packet is therefore a boundary theorem, not a chamber consumer.

## Definitions and assumptions

### Probability and stopping

- Before termination, the only public history is repeated all-Continue.
  A behavioral strategy therefore induces a complete law on `Nbar`.
- Players' behavioral randomizations are the standard independent
  randomizations of the quitting game. Terminal payoff is expectation under
  the resulting product of complete stopping laws.
- At the first finite date at which somebody Quits, every player Quitting at
  that date belongs to the terminal coalition. If everyone chooses Never,
  the project terminal convention is used.
- `T_k>=r` means that player `k` does not Quit strictly before `r`.

### Agency and deviations

- Prescribed profiles may be arbitrary behavioral profiles.
- `V_P(q)` replaces only the observer by one pure stopping time and leaves all
  opponents literal.
- `B_i(P)` ranges over every unilateral behavioral replacement, not a bounded
  controller class. Since terminal payoff is affine in the observer's
  complete stopping law, its supremum is the supremum of the pure-time menu.
  No cap attainment is used in the switch extraction.
- Reset movers are opponents of the observer. A reset edge mixes complete
  stopping laws; it is not asserted to be chronological play.

### Exact finite cube localization

Let `E={e_1,...,e_m}` be ordered, put `A_j={e_1,...,e_j}`, and let
`F:2^E -> Real`. Define

```text
Sq(F;A;e,f)=F(A+e+f)-F(A+e)-F(A+f)+F(A).
```

Then

```text
F(E)-F(empty)-sum_k [F({e_k})-F(empty)]
 = sum_{1<=j<k<=m} Sq(F;A_{j-1};e_j,e_k).            (14)
```

Thus a macro-minus-star remainder is exactly a sum of `binom(m,2)` literal
contextual squares.

On a complete-law reset cube, every prescribed terminal payoff and every
fixed pure-time deviation payoff is separately affine in the reset laws. If
two effective reset amplitudes are `alpha_e,alpha_f`, its contextual square
is exactly their product times the full-target four-corner rectangle. Hence

```text
|Sq| <= 4M alpha_e alpha_f
     <= 4M C^2 lambda_n^2.                           (15)
```

Consequently a persistent first-order debt square, after paying the
prescribed-payoff term, is a first-order unrestricted-cap square. The checked
supremum-switch certificate cited below then supplies (4). Theorems A and B
start from that actual certificate; they do not assume that a best response
attains the cap.

## Source correspondence

No paper or literature theorem is used in this packet.

The following ingredients are already checked in Lean.

- Complete stopping-law mixing and payoff affinity:
  `quittingStoppingLawMixtureBehaviorStrategy`,
  `quittingBehaviorStoppingLaw_stoppingLawMixture`, and
  `quittingTerminalPayoff_update_stoppingLawMixture_eq` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`.
- Exact cube localization and multi-affine square bounds:
  `QuittingStoppingLawResetCubeData.endpoint_sub_source_sub_frozen_eq_squareCurvatureSum`,
  `quittingTerminalPayoff_resetCube_square_eq_scale_mul_scale_mul`,
  `abs_quittingTerminalPayoff_resetCube_square_le`, and
  `quittingPureTimeDeviationPayoff_resetCube_square_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCube.lean`.
- Supremum switching without cap attainment:
  `QuittingPureTimeWitnessSwitchCertificate` and
  `exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`.
- Literal reset-square provenance and its static-orientation warning:
  `QuittingPureTimeResetSquareEdgeWitnessSwitch` and
  `exists_resetCubePureTimeSquareEdgeWitnessSwitch_of_abs_debtCurvature` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawResetCubeOrientation.lean`.
- Conversion of a positive pure-time edge to a paid row:
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`.
- The ordinary full-opponent survival identity for a paid row:
  `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` in
  `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.
- The finite-splice error and its terminal product:
  `quittingFiniteSpliceError`,
  `tendsto_quittingFiniteSpliceError_terminal`, and
  `exists_finiteSpliceCutoffs_tendsto_zero_of_capTight` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSplice.lean`.
- Exact Never-pattern classification:
  `quittingPairDeletedSurvivalLimit_eq_prod_neverMass`,
  `quittingMaxPairDeletedSurvivalLimit_eq_zero_iff_two_zeroNever`, and
  `tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteCapClock.lean`.

The following content is new ordinary mathematics and is not claimed checked:

1. the deleted-mover friction bounds (2)--(3);
2. their source transfer and weak pair-Never consequence (6)--(11);
3. full-chord descaling from (5) to the fixed gain (8); and
4. the exact all-proper regression below.

The checked generic paid-cap structures are relevant only to the scope audit.
`QuittingPaidCapLiftedSource.nonempty_summablePort` in
`Endpoint/PaidCapLiftedSummablePort.lean` and
`QuittingPaidCapLiftedSource.exactTrichotomy` in
`Endpoint/PaidCapPortExactTrichotomy.lean` accept the paid endpoint, but do
not store its reset-cube provenance. Furthermore,
`HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` in
`Endpoint/ActualProfileTerminalGapPaidCap.lean` already supplies a generic
paid-cap port at every actual profile under the maintained terminal-gap and
positive-minimum data. Merely entering that trichotomy is not new progress.

## Proof

### 1. Cube identity and fixed-witness budget

Telescope `F(E)-F(empty)` along the order `e_1,...,e_m`. For each `k`, move
the background of the `e_k` edge successively through
`e_1,...,e_{k-1}`. The change caused by inserting `e_j` is exactly
`Sq(F;A_{j-1};e_j,e_k)`. Summing first in `j` and then in `k` proves (14).

Separate affinity of expected terminal payoff in each complete stopping law
factors a two-coordinate square as `alpha_e alpha_f` times a four-corner
rectangle. Every corner lies in `[-M,M]`, so the rectangle has absolute value
at most `4M`. This proves (15), both for the prescribed payoff and after the
observer is replaced by any fixed pure time. The existing oriented-supremum
lemma can therefore choose two pure times and a diagonal satisfying (4) from
a first-order cap square while using arbitrarily small approximate-maximizer
errors. No maximizer is required.

### 2. Deleted-mover friction

Separate affinity in mover `h` gives the exact identity

```text
G(P')-G(P)
 = alpha [G(P[h<-nu])-G(P[h<-mu])].                  (16)
```

Condition on the stopping times of all opponents other than `i,h`. If one of
them stops strictly before `r`, the two observer deviations have behaved
identically before absorption, so each endpoint gap is zero. On the remaining
event each endpoint gap lies in `[-2M,2M]`; their difference is at most `4M`.
The probability of the remaining event is (1), proving (2).

For (3), continue conditioning on that event. Under endpoint law `mu`, the
gap also vanishes if `h` stops before `r`, and otherwise has absolute value at
most `2M`. Its conditional absolute expectation is thus at most
`2M mu([r,Never])`; the analogous bound holds for `nu`. Apply the triangle
inequality in (16). This proves (3). Because event (1) omits `h`, reversing
the reset edge does not change the survival factor.

### 3. Rectangle localization and source transfer

Join `S_n` to `R_n` by the two literal reset edges of their square. Their two
signed `G_n` increments sum to the right side of (4). Hence one has absolute
value at least `gamma lambda_n/2`, proving (5). Its effective amplitude is
positive; otherwise the edge increment would vanish.

Apply (2) and `alpha_n<=C lambda_n` to this edge:

```text
gamma lambda_n/2
 <= 4M C lambda_n H_{-i,-h}(P_n,r_n).
```

Cancel the positive `lambda_n` to obtain (6). There are finitely many mover,
orientation, and face-context labels, so a subsequence fixes them.

Returning a reset coordinate to its source law changes the probability of
any event by at most that coordinate's mixture amplitude. Telescope over at
most `m` coordinates. The total change is at most `mC lambda_n`; for all
sufficiently large `n` it is at most `gamma/(16MC)`. Combining this with (6)
proves (7).

If `r_n` is bounded, pass to a constant subsequence. Otherwise pass to one on
which `r_n->infinity`. In the latter case, compactness of `Nbar` gives a weakly
convergent subsequence of the finitely many common-source laws outside
`{i,h}`. For each fixed `N`, eventually `r_n>N`, and (7) implies probability
at least `gamma/(16MC)` that all those players stop after `N`, with Never
included. This tail set is clopen in `Nbar`, so the inequality passes to the
weak limit. Let `N` increase. Continuity from above gives (11).

### 4. Full-chord descaling and post-mark mass

On the selected edge, (16) and (5) give

```text
|G_n(P_n[h<-nu_n])-G_n(P_n)|
  >= (gamma lambda_n/2)/alpha_n
  >= gamma/(2C).                                     (17)
```

At least one endpoint has absolute `G_n` value at least half of (17). Orient
the two pure times at that endpoint so the value is positive. This proves
(8), and the existing first-disagreement constructor supplies the paid row.

The paid gap (8) itself vanishes unless every opponent survives strictly
before `r_n`. Its absolute value is at most `2M` on that event. Therefore the
same paid endpoint `E_n` satisfies

```text
gamma/(4C)
 <= 2M Pr_{E_n}(T_k >= r_n for every opponent k != i),
```

which proves (9), and independence factors this full survival as (10).

For comparison, applying the sharper edge bound (3) directly to (5) gives

```text
H_{-i,-h}(P_n,r_n)
 [mu_n([r_n,Never])+nu_n([r_n,Never])]
 >= gamma/(4MC).                                     (18)
```

At least one endpoint contributes half, consistently with (9)--(10). Notice
that the factor in either formulation is an inclusive moving post-mark tail.
In finite-splice notation its mover factor is

```text
StopMass_h(r_n)+LateFiniteMass_h(r_n)+NeverMass_h.   (19)
```

It may be carried entirely by a finite atom at the mark. Equations (10)--(11)
therefore do not imply the actual terminal product (12).

### 5. Exact Fin4 regression

Take players `i,a,b,c`, with `i` the observer and `a,b` the reset movers. For
`n>=2`, set

```text
r_n=n,   lambda_n=1/n,   K_n=n^3,
delta_n=1/K_n,           L_n=2n.
```

At the common source:

- `a` is uniform on `{L_n,...,L_n+K_n-1}`;
- `b` stops surely at `L_n+K_n`;
- `c` stops surely at `L_n+K_n+1`; and
- `i` may be prescribed Never.

The full target of each of `a,b` stops surely at `r_n`. Mix `a`'s source law
with its target at weight `x` and `b`'s at weight `y`, where the reset-square
corners have `x,y in {0,lambda_n}`.

Give `a,b,c` reward zero at every terminal coalition. Give observer `i`
reward one exactly on

```text
{i,a},  {i,a,b},  {b},  {a,b},
```

and zero on every other terminal coalition. This is one reward table,
independent of `n`, and has `M=1`.

Direct conditioning yields the complete pure-time menu for `i`:

```text
Quit at r_n:                            x.
Quit strictly between r_n and L_n:     y.
Choose Never:                          y.
Quit in a's source window:
                    y+(1-x)(1-y)delta_n.
Every other pure time: no larger than one of these.
```

For the window formula, the term `y` is the event that `b` uses its target at
`r_n`; otherwise a payoff one occurs exactly when neither reset target is
used and `a`'s uniform source clock equals `i`'s chosen window date.

An arbitrary behavioral deviation of `i` is a probability mixture of this
pure menu. Therefore the exact unrestricted cap is

```text
B_i(x,y)=max{x, y+(1-x)(1-y)delta_n}.                 (20)
```

Since `delta_n<lambda_n`, the four values are

```text
B00=delta_n,
B10=lambda_n,
B01=lambda_n+(1-lambda_n)delta_n,
B11=lambda_n+(1-lambda_n)^2 delta_n.
```

Thus

```text
B11-B10-B01+B00
 = -lambda_n+(1-lambda_n+lambda_n^2)delta_n,
```

whose ratio to `lambda_n` tends to `-1`.

For any fixed pure time, its square is zero unless the time lies in `a`'s
source window. There its value function is

```text
y+(1-x)(1-y)delta_n,
```

whose square is exactly `delta_n lambda_n^2`. Hence the supremum of all
fixed-time square magnitudes is `delta_n lambda_n^2=o(lambda_n)`. The active
cap responses are `r_n` and a date in the moving window. Their first
disagreement tends to infinity, while all opponents survive strictly before
`r_n` with probability one at every source and full-target endpoint.

Every displayed law of `a,b,c` has finite support, including every face
mixture. Its Never mass is exactly zero. In particular, for either reset
mover the moved-law factor in (12) is zero. More strongly, after deleting any
two players, at least one of `a,b,c` remains and has zero Never mass, so every
terminal pair-deleted survival limit is zero as well. The checked zero-pattern
classification places every index in the cap-tight finite-splice arm.

Nevertheless all finite stopping dates escape. The source, target, and face
laws converge weakly to Never laws, producing the compact pair-Never atom in
(11). This proves that the compact atom is not the actual cemetery factor
used by finite splicing.

Finally, Never mass is affine under complete-law mixing:

```text
Never((1-alpha)mu+alpha nu)
  =(1-alpha)Never(mu)+alpha Never(nu).                (21)
```

The class of proper laws is therefore invariant under every finite Boolean,
radial, rebased, or active-face mixture whose inputs are proper. This proves
the final assertion of Theorem C.

## Boundary tests

1. **Positive terminal splice obstruction.** If a moved law has Never mass
   `p>0` and its maximal terminal pair-deleted survival is `s>0`, the checked
   finite-splice error tends to `ps>0`; no cutoff sequence can make that
   universal error vanish. The regression does not dispute this theorem.
2. **Mass exactly at the disagreement mark.** The factor forced by (3) is
   inclusive. It may equal one because the full target stops surely at
   `r_n`, while `LateFiniteMass(r_n)=NeverMass=0`. This tests why (19), not a
   cemetery-only expression, is the exact conclusion.
3. **Bounded disagreement.** If the integer sequence `r_n` is bounded, a
   constant subsequence gives a fixed finite reached row. The weak Never
   conclusion (11) is asserted only in the escaping branch.
4. **Deleted versus full reach.** Bound (2) omits the changed mover. It does
   not by itself give full opponent survival. The sharper bound (3) restores
   the mover only at one full-chord endpoint, yielding (9), not a terminal
   survival limit.
5. **All-proper falsifier.** The exact table in Proof 5 has first-order cap
   curvature and unit reach at the moving row, but zero actual Never factor
   everywhere. It rules out (13) while respecting unrestricted behavioral
   deviations.
6. **Scope of the falsifier.** The regression has global semantic-debt
   minimum zero and is not a positive-minimum hard source. It falsifies the
   proposed local implication from a cap-switch rectangle to finite-splice
   cemetery mass; it does not falsify the full Jensen question or the Fin4
   conjecture.

## Adapter and consumer

The actual-data adapter is the existing reset-cube chain:

```text
QuittingStoppingLawResetCubeData
 + source-matched first-order debt/cap square
 + O(lambda_n^2) prescribed and fixed-time square budgets
 -> QuittingPureTimeWitnessSwitchCertificate
 -> literal two-edge square path satisfying (4).
```

The checked declarations named in the source audit supply every step through
the switch certificate and literal reset-edge provenance. Theorems A and B
are the new ordinary-math adapter from that certificate to the linked
full-chord paid row and pair-deleted/post-mark packet.

There is deliberately no claimed downstream chamber consumer. The strict
conjecture-facing output is instead the exact negative answer to the proposed
finite-splice subroute (13), which narrows the positive-curvature obligation
in `FIN4_JENSEN_CLOCK_SELECTION_AND_CAP_LEAKAGE.md`.

Although the fixed-gain endpoint can instantiate
`QuittingPaidCapLiftedSource`, that generic structure does not retain the
reset cube, original common source, full-target ancestry, or survival packet.
Under the maintained terminal exploitability gap, a generic paid-cap port was
already available at every actual profile. Its charged/descent/inert
trichotomy is therefore neither a new consumer nor an ancestry-preserving
continuation of this packet. The precise surviving target is:

```text
consume the curvature-selected endpoint and its source-attached packet
without forgetting their common reset-cube ancestry.                 (22)
```

## Lean handoff

The narrow formalization can be split into four declarations without adding
a speculative state machine.

1. Prove a generic edge estimate, suggested shape

   ```text
   abs_quittingPureTimeGap_update_stoppingLawMixture_sub_le_pairDeleted
   ```

   taking two pure times, their first-disagreement date, one off-observer
   mover, and one complete stopping-law mixture. Prove both (2) and the
   inclusive-tail refinement (3). Reuse stopping-law payoff affinity and the
   product survival definitions; do not encode the inequality as a structure
   field.
2. Define a small output structure retaining an existing
   `QuittingPureTimeWitnessSwitchCertificate`, its literal
   `QuittingStoppingLawResetCubeData`, selected square path, selected full
   target, and the resulting `QuittingPaidFirstDisagreementRow`. Prove the
   constants (5)--(10) from the generic edge estimate and exact mixture
   scaling. In particular, retain the original cube data rather than coercing
   immediately to `QuittingPaidCapLiftedSource`.
3. Add the sequence corollary giving the common-source floor (7) and weak
   pair-Never conclusion (11). The only topology needed is weak convergence
   on the compact countable one-point space and continuity of its clopen
   tails.
4. Formalize the regression on `Fin 4`. Define the reward table by the four
   listed coalitions and define the finite-support hazards realizing the
   source and target clocks. Prove the pure-menu formula (20), use behavioral
   pure-time extremality for the cap, normalize the symbolic square, and
   discharge the finite-splice side with
   `tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern`.

Useful exact finite checks are the four evaluations of (20), the identity
that the window fixed-time square is `delta_n lambda_n^2`, and the zero-Never
facts for every face mixture. No approximate numerical solver, cap-attainment
axiom, or new global projective architecture is needed.

## Scope and nonclaims

- The packet does not produce cap curvature from every Fin4 positive-minimum
  source. It consumes a supplied source-matched rectangle certificate.
- It does not place the full-chord endpoint on the minimum fibre or bound the
  other players' cap increments.
- A reset-square edge is static geometry, not a chronological edge of play.
- The weak pair-Never atom is pair-deleted and belongs to a compact limit; it
  is not an actual full terminal-law atom.
- The moving post-mark mass may be entirely finite or concentrated at the
  disagreement mark.
- The paid-cap trichotomy forgets the ancestry which is essential here and
  may end in its known inert arm. This packet makes no chamber-consumer claim.
- The all-proper regression is not a positive-minimum counterexample and does
  not settle the Jensen question, Fin4, or the finite-quitting conjecture.
- No uniform-equilibrium payoff is constructed.

## Lean formalization record

Pre-formalization packet SHA-256:
`ccc5344f7e837856c725ded574610fd5d228ec3dae3d225eadeb84d363eb32b0`.

The friction, full-chord, compact-limit, source-transfer, and finite-splice
layers landed in commit
`7d104695842528df0949711af7418a7226c6fec7`; the named regression asymptotics
landed in commit `62aa688b80f14fab63df0cedcf69c7a878d1c64f`.
The production owners are
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchFriction.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchFullChord.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchSourceTransfer.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchCompactLimit.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSplice.lean`,
and
`UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourCapSwitchAllProper.lean`.

The principal checked declarations are
`abs_quittingNormalizedPureTimeGap_update_stoppingLawMixture_sub_le`,
`abs_quittingNormalizedPureTimeGap_update_stoppingLawMixture_sub_le_coarse`,
`exists_quittingCapSwitchFullChordPaidRow_of_firstOrderRectangle`,
`abs_quittingPairDeletedSurvivalWeight_resetCube_profile_sub_source_le`,
`nonempty_quittingEscapingPairDeletedStoppingLawLimit`,
`nonempty_quittingEscapingPairDeletedStoppingLawLimit_resetCubeSource`,
`quittingCounterfactualPureTimeCap_square`,
`fixedResponse_square_eq`,
`finiteSplice_terminalProduct_eq_zero`,
`tendsto_quittingFiniteSpliceError_reconstructedHazard_zero`,
`tendsto_quittingCounterfactualPureTimeCapSquare_div_lambda_neg_one`,
`tendsto_uniformFixedResponseSquareBound_div_lambda_zero`,
`tendsto_mark_shift_atTop`,
`stoppingLaw_survival_laws_mark_eq_one`, and
`prod_opponent_stoppingLawSurvival_laws_mark_eq_one`.
The first-order wrapper retains the literal deleted-survival floor
`charge / (8 * bound * constant)` and paid full-chord gain
`charge / (4 * constant)`.

Evidence seals are `M` and `L`.  The reset cube, edge witness, and source
sequence are supplied inputs, so there is no unconditional source `A`.
There is no downstream `C`: no theorem produces the required source-matched
rectangle from a positive-minimum or hard-residual branch, renews the paid
row, or consumes the compact pair-deleted Never product.  The weak product is
pair-deleted rather than a full terminal-law atom, and moving post-mark mass
may be finite or concentrated at the mark.  The regression is all-proper and
has zero finite-splice cemetery product; it is not a positive-minimum
counterexample.  No chamber conclusion, recursive closure, terminal
approximation, or uniform-equilibrium payoff is produced.
