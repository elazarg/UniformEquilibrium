# Safe HOPF completion chambers and a full-support stationary closure

Authors: `CODEX_HOPF`, `CODEX_AMPERE`

Independent reviews:

- [`CODEX_CURIE`](../feedback/CODEX_HOPF__HOPF_COMPLETION_SAFE_BASE_CHAMBERS__BY_CODEX_CURIE.md)
- [`CODEX_RIEMANN`](../feedback/CODEX_AMPERE__HOPF_OWNER_UNSAFE_STATIONARY_CLOSURE__BY_CODEX_RIEMANN.md)

## Exact statement

Let the players be `Fin 4`, written `0,1,2,3`, and let

\[
A=\{0,1,2\}.
\]

The following statements hold for ordinary finite quitting games with zero
payoff after infinite continuation.

### Theorem A: safe singleton and pair chambers

Assume

\[
r_0(\{0,2\})-r_0(\{2\})=-2,
\qquad
r_1(\{1,2\})-r_1(\{2\})=-2,
\qquad
r_2(\{2\})=0.
\tag{A1}
\]

Put

\[
J_{32}=r_3(\{2,3\})-r_3(\{2\}).
\]

If \(J_{32}\le0\), the pure date-zero coalition `\{2\}`, followed
counterfactually by all-Never, is an exact terminal Nash profile against
every unilateral behavioral deviation.  In particular the game has a
uniform-equilibrium payoff and global minimum terminal debt `D_*=0`.

If instead \(J_{32}>0\) and

\[
r_2(\{2,3\})\ge r_2(\{3\}),
\tag{A2}
\]

\[
r_i(\{2,3\})\ge r_i(\{i,2,3\})
\qquad(i=0,1),
\tag{A3}
\]

then the pure date-zero coalition `\{2,3\}` is an exact terminal Nash
profile against every unilateral behavioral deviation.

More generally, fix player `2` to Quit and let the other three players play
the induced finite binary game `Gamma_2`.  For a mixed Nash equilibrium
`pi` of `Gamma_2`, let `mu_pi` be its product distribution over the free
quitting set `T subseteq \{0,1,3\}` and put

\[
Q_2(\pi)=\sum_T\mu_\pi(T)r_2(\{2\}\cup T),
\tag{A4}
\]

\[
C_2(\pi)=\sum_{T\ne\varnothing}\mu_\pi(T)r_2(T).
\tag{A5}
\]

If `Q_2(pi) >= C_2(pi)`, the induced mixed root with player `2` surely
Quitting, followed by all-Never, is an exact terminal Nash profile against
all behavioral deviations.  Consequently, if `D_*>0`, compactness of the
finite induced Nash set forces one uniform margin

\[
\exists\eta>0\ \ \forall\pi\in\operatorname{Nash}(\Gamma_2),
\qquad C_2(\pi)-Q_2(\pi)\ge\eta.
\tag{A6}
\]

### Theorem B: the sharp owner-unsafe completion is stationary-safe

Fix

\[
d=\frac1{100},\qquad L=\frac{39}{100},
\qquad 0<R\le\frac1{37},\qquad s>0.
\tag{B1}
\]

The following formulas define a complete reward table.  For each active
recipient `i in A` and background `T subseteq Fin 4 \setminus \{i\}`, first
define its passive value `p_i(T)` by

\[
p_0(T)=
\begin{cases}
-\frac12\mathbf1_{1\in T}+\mathbf1_{2\in T},&3\notin T,\\
0,&3\in T,
\end{cases}
\tag{B2}
\]

\[
p_1(T)=
\begin{cases}
-\frac12\mathbf1_{0\in T}+\mathbf1_{2\in T},&3\notin T,\\
d-1,&T=\{0,3\},\\
0,&3\in T\text{ and }T\ne\{0,3\},
\end{cases}
\tag{B3}
\]

\[
p_2(T)=
\begin{cases}
-\frac15(\mathbf1_{0\in T}+\mathbf1_{1\in T}),&3\notin T,\\
0,&3\in T.
\end{cases}
\tag{B4}
\]

Define the membership gains

\[
g_0(T)=\mathbf1_{1\in T}-2\mathbf1_{2\in T}
       +d\mathbf1_{3\in T},
\tag{B5}
\]

\[
g_1(T)=\mathbf1_{0\in T}-2\mathbf1_{2\in T},
\tag{B6}
\]

\[
g_2(T)=\frac25(\mathbf1_{0\in T}+\mathbf1_{1\in T})
       -L\mathbf1_{3\in T}.
\tag{B7}
\]

For `i in A`, set

\[
r_i(T)=p_i(T),
\qquad
r_i(T\cup\{i\})=p_i(T)+g_i(T).
\tag{B8}
\]

For player `3`, on every nonempty `T subseteq A`, set

\[
r_3(T)=s+R\mathbf1_{0\in T}-(R+1)\mathbf1_{1\in T},
\tag{B9}
\]

put `r_3(\{3\})=s`, and set

\[
r_3(T\cup\{3\})=r_3(T)
 -\mathbf1_{0\in T}-\mathbf1_{1\in T}+\mathbf1_{2\in T}
\qquad(T\ne\varnothing).
\tag{B10}
\]

Then this table has a full-support stationary exact terminal Nash profile
against every unilateral behavioral strategy.  Therefore it has a
uniform-equilibrium payoff and

\[
\boxed{D_*=0.}
\tag{B11}
\]

The conclusion is uniform over all parameters in (B1), and persists on an
open neighborhood of these tables.

For the special value of `R` arising from the HOPF maximal-ray recurrence,
the same table simultaneously has all of the following:

- the literal paid transition `\{3\} -> \{0,3\}`;
- zero pair defect for player `0` and distinct positive pair defects for
  players `1` and `2`;
- a globally maximum, partial-current-support ballistic exact-cap ray;
- full binding at the limiting cap;
- all-Continue as the unique limiting exact cap root;
- no pure terminal-coalition equilibrium; and
- a uniform owner-unsafe induced-base margin `39/100`.

Thus none of these local inert/maximal-ray properties prevents a finite-scale
full-support stationary equilibrium.

## Proof of Theorem A

Prescribe exactly player `2` to Quit at date zero and all players to play
Never after the counterfactual all-Continue outcome.  A unilateral deviation
by player `0`, `1`, or `3` cannot prevent player `2` from Quitting.  The game
therefore ends at date zero, and the deviator's whole behavioral strategy
reduces to its mixture between its two date-zero endpoint actions.  The three
Quit-minus-Continue gains are the two values `-2` in (A1) and \(J_{32}\).

If player `2` deviates to Continue, every opponent plays Never.  Every later
finite Quit pays `r_2(\{2\})=0`, and Never also pays zero.  Hence \(J_{32}\le0\)
proves exact Nash against the full behavioral strategy class.

For `\{2,3\}`, every unilateral deviation still leaves another sure quitter.
The two member no-leave inequalities are \(J_{32}>0\) and (A2); the two outsider
no-join inequalities are (A3).  This proves the pair result.

For the induced mixed result, player `2` again screens every free player, so
their full behavioral optimizations reduce exactly to their two actions in
`Gamma_2`.  If player `2` Continues, a nonempty free quitting set pays the
corresponding term in (A5); if every free player Continues, all later finite
Quits and Never pay zero.  Thus player `2`'s two values are exactly (A4)--(A5).
The claimed profile is exact when `Q_2>=C_2`.  The finite induced Nash set is
nonempty and compact, and `C_2-Q_2` is continuous.  If exact equilibrium is
forbidden, its strictly positive minimum is the margin in (A6).

## Proof of Theorem B

Let `x=(x_0,x_1,x_2,x_3)` be a stationary hazard vector and define

\[
s_i(x)=\prod_{j\ne i}(1-x_j),\qquad h_i(x)=1-s_i(x).
\]

Let `Q_i` and `N_i` be player `i`'s Quit-now and Never payoffs against the
stationary opponents.  If `A_i` is the unconditional passive contribution
of nonempty opponent coalitions and `\bar g_i` is the expected membership
gain, then

\[
F_i(x):=h_i(Q_i-N_i)=h_i\bar g_i-s_iA_i.
\tag{B12}
\]

Direct substitution of (B2)--(B10) gives

\[
\begin{aligned}
F_0={}&h_0(x_1-2x_2+dx_3)
 -s_0(1-x_3)(-\tfrac12x_1+x_2),\\
F_1={}&h_1(x_0-2x_2)\\
&-s_1\left((1-x_3)(-\tfrac12x_0+x_2)
 +(d-1)x_0x_3(1-x_2)\right),\\
F_2={}&h_2(\tfrac25(x_0+x_1)-Lx_3)
 -s_2(1-x_3)(-\tfrac15(x_0+x_1)),\\
F_3={}&h_3(-x_0-x_1+x_2)
 -(1-x_0)(1-x_1)(1-x_2)
       (Rx_0-(R+1)x_1).
\end{aligned}
\tag{B13}
\]

The singleton level `s` cancels from `F_3`; hence these polynomials are valid
for every `s>0`.

Put

\[
\begin{aligned}
c={}&(363/2000,\ 4359/20000,\ 5549/50000,\ 583/1250),\\
q={}&(3/2000,\ 7/4000,\ 3/2000,\ 13/5000),
\end{aligned}
\tag{B14}
\]

and let

\[
K=\prod_{j=0}^3[c_j-q_j,c_j+q_j]\subset(0,1)^4.
\]

Let `F` be the column vector in (B13) and put `G=AF`, where

\[
A=\begin{pmatrix}
-3111/10000&2273/10000&-3/250&-10311/10000\\
1021/1000&-10619/10000&451/10000&-10923/10000\\
-1725/10000&-5358/10000&54/10000&-5571/10000\\
591/1000&-6953/10000&-30444/10000&-17754/10000
\end{pmatrix}.
\tag{B15}
\]

This matrix is invertible because

\[
\det A=\frac{443076546006639}{156250000000000}>0.
\tag{B16}
\]

The following is an exact rational interval certificate.  At `R=1/74`,

\[
10^6G(c,1/74)\in[-6,-5]\times[30,31]\times[5,6]\times[25,26].
\tag{B17}
\]

On `K times [0,1/37]`, outward rational evaluation gives

\[
AD_xF\in
\begin{pmatrix}
[.976,1.024]&[-.028,.028]&[-.020,.020]&[-.004,.004]\\
[-.035,.035]&[.965,1.035]&[-.040,.040]&[-.014,.014]\\
[-.018,.018]&[-.015,.015]&[.984,1.017]&[-.005,.005]\\
[-.054,.054]&[-.058,.058]&[-.038,.038]&[.980,1.020]
\end{pmatrix},
\tag{B18}
\]

and

\[
A\partial_RF\in
[-.024,-.019]\times[-.025,-.020]
\times[-.013,-.010]\times[-.041,-.033].
\tag{B19}
\]

Every decimal endpoint in (B18)--(B19) is a terminating rational rounded
outward.  The mean-value bound from (B17)--(B19) gives, for every
`R in [0,1/37]`,

\[
\begin{array}{c|cc}
j&G_j\text{ on }x_j=c_j-q_j&G_j\text{ on }x_j=c_j+q_j\\ \hline
0&\le-1/1000&\ge1/1000\\
1&\le-1/1000&\ge1/1000\\
2&\le-1/1000&\ge1/1000\\
3&\le-1/1000&\ge1/1000.
\end{array}
\tag{B20}
\]

Apply Poincare--Miranda to `-G` on the affine unit-cube presentation of `K`.
There is `x^star in K` with `G(x^star)=0`.  Invertibility of `A` gives

\[
F_i(x^\star)=0\qquad(i=0,1,2,3).
\tag{B21}
\]

Every coordinate of `x^star` is strictly positive.  Hence each player's
stationary opponents absorb almost surely.  Against an arbitrary randomized,
calendar-dependent, history-dependent, Never, or arbitrarily late strategy,
the deviator's terminal payoff is a convex combination of exactly `Q_i` and
`N_i`: the opponents' current stationary draw is fresh and independent at
the absorbing date.  Equation (B21), with `h_i>0`, gives `Q_i=N_i`.  Thus no
behavioral deviation improves.  The full-support stationary profile is exact.

Strictness of (B20) and continuous dependence on the reward table give the
open-neighborhood statement.

For the HOPF orbit value, the standard estimates

\[
t_k\le\frac54b_k,qquad b_{k+1}\le\frac12b_k,
\qquad b_0=\frac1{100},qquad 0<z_k<t_k
\]

give

\[
\sum_kt_k\le\frac1{40},qquad
P_{k+1}=\prod_{h\le k}(1-t_h)^2(1-z_h)\ge\frac{37}{40},
\]

and therefore

\[
0<R=\sum_k\frac{t_k}{P_{k+1}}\le\frac1{37}.
\]

So the specific maximal-ray completion lies in Theorem B's stationary-safe
family.

## Conjecture-facing change

This closes two substantial completion chambers around the reviewed HOPF
strict-ray regression.

The safe sign \(J_{32}\le0\) cannot support positive global debt because a pure
singleton is exact.  Escaping that sign, eliminating every pure terminal
coalition, satisfying the entire induced owner-unsafe margin, preserving a
globally maximal ballistic ray, and making all-Continue the unique limiting
cap root still do not produce a counterexample: the explicit sharp family has
a full-support stationary exact equilibrium in an open hazard box.

Therefore a negative Fin4 construction based on this mechanism must also
remove the finite-scale stationary indifference zero.  Local limiting-root,
binding, and pure-coalition screens are insufficient.

## Source correspondence

The all-behavior pure-coalition formulas correspond to
`quittingTerminalSemanticDebt_pureSetRoot_eq` and
`isεAsymptoticNash_pureSetRoot_iff_forall_mem_notMem` in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

The induced-base construction overlaps
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_or_singletonBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
The new content is its exact HOPF sign specialization and explicit
all-Never-tail equilibrium.

The stationary proof uses existing checked infrastructure:

- `exists_cube_zero_interior_of_strict_opposite_face_signs` in
  `MathUE/Topology/PoincareMirandaCube.lean`;
- `quittingFaceNumerator` in
  `UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`; and
- `quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero` in
  `UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean`.

The exact parameterized reward table, preconditioned face certificate, and
connection to the sharp HOPF completion are new relative to those generic
declarations.

## Boundary tests

- \(J_{32}=0\) is included in the pure-singleton chamber; player `3` is then
  indifferent and arbitrary behavioral mixing does not improve.
- When \(J_{32}>0\), the pair `\{2,3\}` is exact exactly under the displayed
  member/outsider inequalities.
- The table in Theorem B has \(J_{32}=1\), positive spectator singleton, no pure
  terminal coalition equilibrium, unique limiting all-Continue cap root, and
  induced owner-unsafe margin `39/100`.  It therefore lies strictly beyond
  all of the preceding pure/induced screens.
- The certified stationary zero is interior, so all opponents contract and
  the unrestricted-strategy compiler applies without a Never-boundary case.
- The strict `1/1000` face margins prove robustness under small reward-table
  perturbations.

## Lean handoff

1. Define the parameterized table (B2)--(B10) over `Fin 4` and derive the four
   face numerators (B13) by extensional simplification.
2. Define the affine hazard box, matrix `A`, and field `-A*F`.
3. Verify (B16)--(B20) by exact rational normalization and interval bounds.
   The independent reviews provide two separate rational enclosures of all
   eight faces.
4. Apply `exists_cube_zero_interior_of_strict_opposite_face_signs` to the
   affine pullback of `-A*F`.
5. Use `det A != 0` to convert `A*F=0` into coordinatewise `F=0`.
6. Feed the positive hazard and numerator zero directly to
   `quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero`.
   Its fields already include exact behavioral terminal Nash and a uniform-
   equilibrium payoff.
7. For Theorem A, prove the four pure-set toggle inequalities and use the
   checked sure-exit-set consumer; do not recreate behavioral deviation
   semantics manually.

## Scope and nonclaims

- Theorem B does not prove that every owner-unsafe HOPF completion is safe.
- The explicit HOPF completion is a zero-minimum regression, not a
  positive-gap table.
- A positive exact root at a limiting cap is not identified with a stationary
  equilibrium; Theorem B obtains the required endogenous fixed-point value
  independently through the face-numerator zero.
- Binding-cardinality three is not used as player deletion.
- No claim is made about arbitrary Fin4 strict rays outside the stated reward
  family and its open perturbative chamber.

## Checked implementation and revisit gate

The export packet at intake had SHA-256
`650927afd84b2f0e0ad2061a0ad2b60fe582c2b8d2fd128e22c837191e7bd309`.
The checked subset was integrated and pushed at repository revision
`14749dc0acb07a1ef40bc03b884da7ce6c704097`.

The integrated implementation has the following exact layers.

1. `UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean` owns the
   generic opponent-coalition expansion.  Its public declarations are
   `quittingEndpointInsertionToggle`,
   `quittingRootQuitPayoff_eq_sum_opponentCoalitionMass`,
   `quittingRootContinuePayoff_eq_sum_opponentCoalitionMass`,
   `quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle`, and
   `quittingContinueProbability_mul_endpointDifference_eq_sum_atoms`.
2. `UniformEquilibrium/Quitting/Classification/Existence/SureExitChambers.lean`
   defines `QuittingPureSingletonChamber` and `QuittingPurePairChamber`.
   Their `terminalNash` and `uniformEquilibriumPayoff` projections compile the
   literal singleton and pair sign conditions into all-behavior terminal Nash
   profiles and uniform-equilibrium payoffs.
3. `UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean` defines
   `QuittingInducedOwnerChamber`, `QuittingInducedOwnerNeverChamber`, and
   `quittingInducedOwnerNeverExcess`.  The declarations
   `QuittingInducedOwnerNeverChamber.zeroTailRootNash`,
   `QuittingInducedOwnerNeverChamber.terminalNash`,
   `QuittingInducedOwnerNeverChamber.uniformEquilibriumPayoff`, and
   `exists_uniformPayoff_or_inducedOwnerNever_continue_sub_quit_pos_gap`
   make the induced-owner exact-Nash and uniform-gap alternatives literal.
4. `UniformEquilibrium/Quitting/Classification/Existence/RationalStationaryFaceBox.lean`
   and
   `UniformEquilibrium/Quitting/Classification/Existence/CenteredStationaryFaceCertificate.lean`
   provide the supplied-certificate compilers
   `QuittingRationalStationaryFaceBox.exists_faceNumeratorZero`,
   `QuittingRationalStationaryFaceBox.nonempty_stationaryCertificate`,
   `QuittingRationalStationaryFaceBox.exists_uniformEquilibriumPayoff`,
   `QuittingCenteredStationaryFaceCertificate.nonempty_stationaryCertificate`,
   and
   `QuittingCenteredStationaryFaceCertificate.exists_uniformEquilibriumPayoff`.
5. `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`
   defines the exact two-parameter `sharpReward` table and its rational box
   certificate.  `quittingFaceNumerator_sharpReward_eq_formula` is the exact
   face-numerator identity;
   `sharpReward_exists_uniformEquilibriumPayoff` gives a uniform-equilibrium
   payoff for every `R ∈ [0, 1 / 37]` and every real singleton level; and
   `exists_fullSupport_sharpStationaryCertificate` returns a literal
   stationary certificate with every hazard in `(0, 1)`.  The certificate
   stores exact terminal Nash against arbitrary behavioral deviations.
6. The direct screens are split into
   `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskySureExitExclusion.lean`,
   `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyPairDefect.lean`,
   `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyCapLimitRootUniqueness.lean`,
   `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourOwnerRiskyInducedOwnerMargin.lean`,
   and
   `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourOwnerRiskyStationaryDebt.lean`.
   Their capstones are
   `isQuittingSureExitSet_sharpReward_iff`,
   `not_isεAsymptoticNash_pureSetRoot_sharpReward`,
   `sharpPurePairDebt_eq`,
   `sharpPurePairDebt_zero_and_distinct_pos`,
   `quittingInducedOwnerNeverExcess_sharpReward_eq`,
   `quittingAllContinueRoot_isNash`,
   `existsUnique_isQuittingRootNash`, and
   `sharpReward_quittingTerminalDebtSumInf_eq_zero`.
7. `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourOwnerRiskyCheckedScreens.lean`
   packages the checked family facts in `checkedScreens`: full-support exact
   stationary closure, zero global terminal-debt infimum, exclusion of every
   pure sure-exit set, the exact paid-pair gains and debt vector, the exact
   induced-owner margin `39 / 100`, and actual existence and uniqueness of the
   exact all-Continue root at the solo cap.

Evidence seals for the packet as a whole are deliberately asymmetric.

- **M:** PASS for the reviewed ordinary mathematics: the pure and induced
  chambers, rational stationary zero, behavioral Nash consumer, perturbative
  argument, and the asserted HOPF specialization are mathematically
  consistent with the packet's stated hypotheses.
- **L:** PARTIAL.  The generic chamber compilers, the exact owner-risky reward
  family, its full-support stationary certificate and uniform payoff, zero
  debt infimum, and all direct screens listed above are proved in Lean and
  integrated.  There is no checked theorem for persistence on an open
  neighborhood of reward tables, and no checked theorem identifying
  `sharpReward` at any parameter with the packet's claimed HOPF maximal-ray
  completion.
- **A:** FAIL for the conjecture-facing HOPF route.  The checked stationary
  theorem starts from the explicitly defined `sharpReward` family and a
  verified rational face certificate.  No actual maximal-ray source is
  transported to that table, parameter, or cap chronology.  In particular,
  the Research declarations `rationalSingletonTwoChamber` and
  `fullBindingSingletonTwoChamber` concern other zero-minimum tables and are
  not such an adapter.
- **C:** PASS for the explicit owner-risky family itself:
  `sharpReward_exists_uniformEquilibriumPayoff` and the stored terminal-Nash
  certificate are literal semantic consumers, while
  `sharpReward_quittingTerminalDebtSumInf_eq_zero` gives the corresponding
  debt conclusion.  It FAILS as a consumer of the claimed HOPF/maximal-ray
  source because the preceding adapter is absent.

Validation at revision `14749dc0acb07a1ef40bc03b884da7ce6c704097`
included the documentation gate, 109 script unit tests, execution of all 33
registered experiments, import-graph, proof-duplicate, reward-bound,
redundant-order, derivable-telescope, and trust checks, and a full
`lake build` of 11,084 jobs.  The generated exhaustive axiom audit was exact.

This packet remains in the revisit queue because two literal claims are not
formalized: a bare source theorem identifying the owner-risky `sharpReward`
family with the stated HOPF maximal-ray construction and a theorem giving an
open reward-table neighborhood of stationary closure.  Neither is implicit in
parameter-uniformity over `R` and the singleton level.  Revisit promotion only
after both statements are specified without hiding a maximal-ray certificate
or a compact-uniform perturbation bound in the hypotheses and are proved in
Lean.  Until then the integrated results establish a strong standalone
stationary-safe regression, not a theorem about the HOPF construction itself.
