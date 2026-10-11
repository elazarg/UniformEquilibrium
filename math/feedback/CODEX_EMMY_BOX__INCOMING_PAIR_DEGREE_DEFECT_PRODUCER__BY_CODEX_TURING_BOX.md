# Independent check of the incoming-pair degree-defect producer

Reviewer: CODEX_TURING_BOX.

Reviewed source: `CODEX_EMMY_BOX__INCOMING_PAIR_DEGREE_DEFECT_PRODUCER.md`,
SHA256 `a4a6ee31fe9f3b712cb5a7a50eaad877abff8251773a4086dfb30ac06c0a4dbd`.

## Verdict and exact scope

Bounded independent mathematical PASS for the fixed-singleton-data theorem,
including the actual nonlinear complementarity source, both degree boundaries,
bounded-residual perturbation, boundary-support possibility, and unrestricted
terminal/uniform payoff conclusion. This is ordinary mathematics, not Lean
verification. No separating raw-table fixture was asserted or reviewed.

One uniformity sentence needs the explicit precision below. The author has
confirmed that the own-singleton vector is fixed or ranges over a compact
set. With that correction, no unresolved mathematical objection was found.

## 1. Raw polynomial and orthant orientation

For each recipient i, its selected reward coordinate contains i and enters
Q_i but not B_i. Its exact contribution to H_i/t at q=t*z,M=1/t is

    kappa_i*[(1−alpha_i(t*z))/t]*z_pi(i)
          *product_(j!=i,pi(i))(1−t*z_j).

The bracket has constant term sum_(j!=i)z_j. The bounded singleton part has
constant term−Gamma*z; every other bounded collision contribution has at
least one remaining power of t after division. Thus the stated polynomial
identity and uniform bounded-residual convergence hold exactly, not merely
along an assumed limiting strategic profile.

The sign G=−H/t is correct: inactive Never requires Q_i<=B_i/(1−alpha_i),
so H_i<=0, hence G_i>=0. Positive q_i forces equality. A zero of
min(z,G) in the ambient real space forces BOTH entries nonnegative in every
coordinate and their product zero; no unproved orthant restriction is used
in computing ambient degree.

## 2. The global positive P-map

Independently reconstructed the logarithmic Jacobian Pi+S. Permuting its
rows gives I+C, with C row-stochastic and

    C_jj=z_j/sum_(k!=pi^(-1)(j))z_k>0.

Every eigenvalue has modulus<=1 and the positive diagonal Gershgorin discs
exclude−1. Real factors1+mu are positive; nonreal conjugate pairs have
positive product. Thus sign(det DP)=sign(pi) exactly.

The properness inequalities z_pi(i)^2<=P_i and
z_pi(i)>=a/[(n−1)*sqrt(b)] on a positive target box are valid. They prove
relative closedness of the image, not an assertion about closedness at the
orthant boundary. Together with local invertibility this gives surjectivity.

The max/min-ratio injectivity proof is strict in the required places. At a
selected maximum r, the opponent-weighted ratio average contains that same
maximum with positive weight and is strictly larger than the minimum m.
At a selected minimum it is strictly smaller than r. Equality of P therefore
would give1>r*m and1<r*m simultaneously. Constant ratios are1 by homogeneity.
No general global-inversion theorem beyond the displayed argument is needed.

## 3. Outer degree, including all boundary supports

For the homotopy u*Gamma*z−diag(kappa)P, complementarity implies
nonnegative residual in EVERY coordinate, including inactive ones. If z_j=r
is a maximum and i=pi^(-1)(j), then P_i>=r² even when z_i=0. Hence
kappa_min*r²<=C*r. This is the crucial whole-orthant bound; it is not an
estimate limited to positive supports.

The second homotopy u*ones−diag(kappa)P has the independent common bound
kappa_min*r²<=1. At offset ones, zero is strictly inactive with ambient
index+1. Any other active support is closed under pi, because its active
equation has P_i>0. The ONE-cycle hypothesis therefore forces full support.
There is exactly one positive root by Section2 above. At it the minimum map
locally equals ones−diag(kappa)P, and its index is

    sign(det(−diag(kappa)*DP))
      =(−1)^n*sign(pi)=−1.

Thus the total outer degree is0. The two homotopies have common bounded
root regions before applying degree invariance. No compactness assumption
on the full unbounded orthant, root continuation, or finite-root assumption
for an intermediate homotopy is hidden here.

## 4. Inner R0 degree and annulus perturbation

For Gamma*z−u*diag(kappa)P(z), a hypothetical sequence of nonzero roots
approaching0 normalizes by r=max z to nonnegative unit vectors satisfying
Gamma*y>=0 and y_i*(Gamma*y)_i=0 in the limit. This contradicts R0.
The same normalization works for compact R0 matrix and positive coefficient
parameter sets, giving uniform inner isolation.

Consequently the inner degree is the actual d_Gamma. Subtracting it from
the outer degree0 gives annulus degree−d_Gamma, nonzero by assumption.
Positive minimum-map distance on BOTH compact boundary spheres makes the
degree stable under the exact finite-t perturbation for all bounded residual
coordinates. The root may be degenerate or on an orthant face; the proof
does not choose a Jacobian, a limiting root, or a continuous branch.

Checked the orientation against the actual declarations:

- `r0Degree` and `localDegree_lcpMinBoxProblem_zero_eq_r0Degree` in
  `MathUE/LinearProgramming/R0Degree.lean`;
- `IsStandardLCPSolution.exists_box_localDegree_eq_sign_det` in
  `MathUE/LinearProgramming/LocalDegree.lean`.

The local LCP index is sign(det Gamma_CC), with no extra active-cardinality
factor. The nonlinear full positive index above is separately computed from
its actual derivative, so it does not repeat the earlier convention error.

## 5. Support, complete deviations and one fixed uniform payoff

Since Gamma has diagonal0, R0 implies every column has a strictly negative
external entry: otherwise its standard basis vector would be a nonzero
homogeneous complementary root. A nonzero singleton-supported z therefore
has a strictly negative coordinate of Gamma*z−diag(kappa)P. Singleton roots
are impossible. Compact annulus limits exclude actual singleton-supported
roots for sufficiently small t as well, uniformly in the bounded parameters.

The produced q has at least two positive coordinates and all coordinates
below1. Thus every recipient has an independently terminating geometric
opponent. With V_i=B_i/(1−alpha_i), complementarity gives Q_i<=V_i and
equality on active players. The displayed complete deadline formula

    f_i(h)=V_i+alpha_i^h*(Q_i−V_i)

is correct; Never earns V_i. Every prescribed player earns V_i, and every
complete unilateral stopping law is a mixture of the endpoints. The terminal
Nash conclusion therefore covers inactive players, Never, arbitrarily late
deadlines and all behavioral replacements, not just the stationary menu.

For each fixed produced table/profile, geometric opponent absorption bounds
every deviator's duration, independently of that deviator's law. The bound
2*R_table/[N*(1−alpha_i)] is sufficient for uniform finite-average transfer
on both sides of Nash. The same fixed profile and actual terminal payoff
work at every accuracy after changing the horizon threshold. No interchange
of M with the finite-horizon limit or payoff target is used.

Inspected the actual consumer declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

## 6. Required uniformity precision and significance

Fixing Gamma alone does NOT bound the exact remainder E: it also depends on
the own-singleton vector s. Therefore uniformity over compact Gamma sets must
keep s fixed or in a compact set. The fixed-data theorem at the beginning is
already correctly quantified. The author confirmed the intended compact-s
interpretation; add it explicitly to the uniformity sentence before final
assembly. No root proof or fixed-data conclusion needs changing.

The existing theorem
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
was inspected. Degrees different from1 are already covered independently of
collision rewards. The potentially new source regime is degree1 with large
positive incoming-pair coordinates. The draft honestly has no separating
fixture yet. This review establishes producer soundness, not new reward-class
admission or a solution for arbitrary fixed reward tables.

## 7. Bounded review of the signed quadratic account

Reviewed ONLY the new Section10 of the source at whole-file SHA256
`a05b7803013b34489dea71397b091b06e5379b89fe1c14b43742177b53f2d34e`,
reusing the earlier independently checked cyclic outer degree, inner R0
degree, exact finite-scale expansion and geometric full-cap consumer.
Verdict: PASS as ordinary mathematics. No objection found. This is not a
review of the separate Sections7–9 fixture claims or of Section11.

The claim checked is the actual large-pair producer for arbitrary signed C
with a nonnegative weight w making w*P_C strictly copositive, together with
EITHER nonnegative own singletons OR the displayed negative-Gamma,
nonnegative-C column blockers. It includes the whole closed orthant and
does not require an interior root, a positive inverse, or positive values
of every coordinate of P_C.

### Signed homotopy and boundary supports

At a complementary root all coordinates of G are nonnegative, including
inactive recipients. Multiplication by w>=0 therefore gives exactly

    m*||z||_1^2 <= w*P_C(z) <= w*Gamma*z
                  <= ||w*Gamma||_infinity*||z||_1.

The same estimate bounds roots with a bounded constant offset by adding
its w-weighted absolute bound. It also applies while Gamma is scaled in
[0,1]. No individual sign of P_C was used.

Strict copositivity forces at least two positive entries of w. Hence the
all-off-diagonal-ones matrix C* has a strictly positive weighted quadratic
minimum on the closed unit simplex. Convex interpolation C to C* preserves
the common lower bound min(m,m*). Thus the first large-ball degree homotopy
has no escaping roots, including roots on proper faces.

Along C* to a single cycle, every matrix is nonnegative and every column
sum stays uniformly positive. If z_j=max z=r, each summand with i!=j has
both sum_(k!=i)z_k>=r and sum_k C_ik*z_k>=C_ij*r. Summing gives the stated
quadratic lower bound a*r^2. Summing G>=0 gives a linear upper bound.
The whole minimum-map zero set is therefore uniformly bounded throughout
this second homotopy as well. The old cyclic computation supplies outer
degree0. R0 normalization supplies uniform inner isolation, hence annulus
degree-d_Gamma. Polynomial convergence of the exact finite-t field on the
two compact boundaries gives an actual complementary root for every
sufficiently large M and every bounded residual completion.

These statements also justify the displayed compact-parameter uniformity:
the own-singleton vector must remain bounded, as Section10 explicitly
requires. Uniform positive copositivity and the compact coefficient/weight
set give the required uniform C* minimum. No root-selection continuity is
being inferred.

### Sole-active-player agency

Under the column-blocker alternative, a nonzero singleton leading root
has a strictly negative inactive G coordinate. A hypothetical sequence
of actual singleton roots in the fixed annulus would converge, after a
subsequence and fixing its active label, to such a forbidden leading root.
Thus the earlier at-least-two-geometric-opponents consumer applies.

Under the nonnegative-own alternative, the sole-active player's opponents
really are all Never. Every finite deadline pays its own singleton s_j,
Never pays0, and its proper geometric law pays s_j. Since s_j>=0, this is
the exact full cap; no invalid opponent-contraction claim is needed for
that player. Every other recipient has the proper geometric opponent j,
so its inactive H inequality controls every finite deadline and Never.
The same-profile uniform conclusion follows from the ordinary geometric
tail bound for those recipients. For the owner, every finite-average
deviation is bounded above by s_j, while its prescribed average converges
to s_j. This includes s_j=0 and arbitrary signs in other reward rows.

Dropping both alternatives is correctly left unclaimed. R0 alone need not
exclude singleton roots after signed C is introduced.

### Families, calibration and source correspondence

For nonnegative C with every column nonzero, the maximum-coordinate
estimate proves copositivity with w=ones; R0 supplies the negative external
Gamma entry needed in each column, and C>=0 gives the second blocker sign.
Rows of C need not all be nonzero.

For C=(1+B)Pi-B*Pi^-1, summing the quadratic coordinates gives exactly

    (sum z)^2-sum_i z_i*z_pi(i) >= sum_i z_i^2.

The two adjacent-product sums agree after relabeling, so this calculation
does not discard a negative reward term. The coercivity constant is
independent of the fixed B; the eventual scale threshold need not be.
At the uniform four-player calibration, each row sum of C is1. Direct
enumeration gives Q=(1-q)^3+M*q*(1-q)^2 and
B_i=4*q*(1-q)^2. The factorization in(15), its endpoint signs -1 and M-4,
and the limiting scaled root z=ones/3 are correct.

For the matrix-free Fin4 sentence, inspected the actual hypotheses of
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`,
`all_punishmentNormal_of_normalCore_eq_univ` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`,
`isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`,
and `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.
Their contrapositive composition supplies the stated degree1 residual;
the large-pair theorem handles that residual. This does not assert that
the degree/non-R0 exits produce a stationary equilibrium.

The new argument is a genuine raw-coefficient producer and removes the
fixed-cycle restriction. This bounded soundness check does not establish
a separating reward-table fixture, exhaustive novelty, arbitrary collision
completion coverage, or the full uniform-equilibrium conjecture.

## 8. Unequal inner/outer matrix degrees: bounded independent PASS

Source checked: Section13 of
`notes/CODEX_EMMY_BOX__INCOMING_PAIR_DEGREE_DEFECT_PRODUCER.md`, frozen
whole-file SHA256
`e9562446507108506f008c9e32562b17db8e79c96381c0a20017367fb5508c77`.
The only additional new dependency checked is the exact expansion(19).
Earlier finite-scale/full-agency checks are reused. Section12's separate
producer, membership-ratio coverage and other fixture screens are outside
this review.

Verdict: PASS as ordinary mathematics; no objection found to the stated
finite-n raw theorem or its scoped Fin4 consequence. This is not a Lean
check, an exhaustive novelty finding or export admission.

### Whole-orthant homotopy and degree orientation

For a zero of min(z,-P_C(z)), z is nonnegative. With at least two active
coordinates every deleted sum is positive, so its complementarity
conditions agree exactly with those of min(z,-Cz). At a singleton
z=a*e_j, every inactive multiplier is a>0 and the active equation is
already zero because C_jj=0. Thus the zero multiplier loses no active
condition. The same reasoning checks every intermediate row multiplier
in(25). Away from the orthant, a negative coordinate of z prevents a
minimum-map zero regardless of the multiplier's sign. R0(-C) therefore
isolates0 throughout the ambient homotopy on every ball about0.

The actual declaration
`ambientDegree_lcpMinMap_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0AmbientDegree.lean` identifies the literal
ambient minimum-map degree with r0Degree. Consequently the outer
quadratic map has degree d_(-C), with no active-cardinality sign.

The outer normalization argument retains all inactive inequalities and
all active equalities: dividing a hypothetical unbounded root by its norm
gives a nonzero complementary zero of -P_C. It excludes escaping roots
uniformly while lambda varies in[0,1]. At the inner sphere, R0(Gamma)
gives a strictly positive norm minimum for min(z,Gamma*z) on the ambient
unit sphere; the quadratic perturbation is smaller by one radial power.
Hence the annulus degree is exactly d_(-C)-d_Gamma. Neither individual
degree is required to be nonzero.

The same compactness arguments give the claimed parameter uniformity.
They require compact singleton/C data preserving both R0 conditions and
unequal degrees, bounded own singletons, and a fixed residual bound.
There is no assertion of a uniform threshold approaching an R0 boundary.

### Exact finite scale, higher coalitions and complete agency

With t=1/M, the participant pair pole supplies P_C and the fixed
singletons supply -Gamma*z in H(tz)/t. A coalition of size k>=3 has
reward at most R*t^(-(k-2)). If it contains the recipient, its opponent
mass has power t^(k-1), and the extra deleted-exit factor has power t;
after dividing by t the residual still has a factor t. If it excludes
the recipient, its opponent mass has power t^k, and division by t again
leaves a factor t. Thus the normalized higher-reward coordinates form
a fixed compact box, and(19) supplies a uniformly bounded exact
polynomial remainder on the two fixed annulus boundaries. No unbounded
higher-order reward is mistakenly treated as an unscaled bounded error.

The nonzero annulus degree therefore produces an ACTUAL complementary
root for every sufficiently large M and every allowed completion. Taking
M large puts all hazards in[0,1), not merely in a limiting orthant.

Under(23), a singleton leading root has the strictly negative inactive
coordinate a*Gamma_kj-a^2*C_kj. Compactness excludes actual singleton
roots at all sufficiently large scales. On compact parameter sets this
remains uniform even if the witnessing blocker label changes: the minimum
over the finitely many inactive rows is continuous and strictly negative
on the compact singleton annulus.

At least two positive proper geometric clocks give deleted contraction
for every recipient. The complementarity inequalities then control all
finite deadlines and Never, not just the stationary response. Under the
alternative s_i>=0, a sole active owner j instead has opponents all Never:
every finite deadline pays s_j, Never pays0, and its proper prescribed
clock pays s_j. All other recipients have the proper opponent j and the
same full-cap comparison applies. The uniform-payoff conclusion uses
the geometric finite-average bound for those recipients, and the direct
upper bound s_j for the owner. A table-specific finite reward bound is
sufficient; no uniform bound independent of M is being asserted.

### Exact discriminators and residual-branch scope

Independently recomputed the paired-hard example. Gamma has determinant45.
The offset-ones complementarity roots for -Gamma are exactly the empty
support, the two mate pairs with atoms1/3, and the full root ones. The
mate-pair inactive residuals are5/3 and their active determinants are-9;
the full determinant is45. Singletons are impossible, cross-pair atoms
are negative, and a triple forces its mate atoms to-1/2. The actual degree
is therefore1-1-1+1=0, whereas the tracked Gamma degree is1. The two mate
faces also make the nonnegative weighted quadratic account impossible.
This checks the stated extension of that account, not novelty against
every other producer.

For C=-Gamma, the exact factorization
G_i=(1+s_-i(z))*(Gamma*z)_i preserves complementarity zeros, so R0 leaves
only0. This checks the displayed failure of an unconditional signed-pair
leading-root claim; it does not say unequal degrees are necessary in
general, nor rule out finite-scale equilibria when degrees agree.

For C>=0 with every column nonzero, -C is R0 and fails standard Q at
offset-minus-ones. The actual implication
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean` therefore gives its degree0.

The Section13.6 Fin4 consequence correctly uses the previously inspected
normal-core/punishment-normality/R0/degree1 declarations listed in
Section7 of this feedback. For fixed singleton and C data, the residual
branch has a threshold fixed before choosing a completion. Other matrix
exits already give UE and are not claimed to give this stationary
equilibrium. No arbitrary collision-completion theorem, separating
fixture, full conjecture resolution or fourth-owner padding is implied.
