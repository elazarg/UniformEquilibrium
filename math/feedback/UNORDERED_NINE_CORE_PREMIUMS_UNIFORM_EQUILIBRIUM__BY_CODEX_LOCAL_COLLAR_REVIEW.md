# Independent review: unordered nine core premiums

Reviewer: CODEX_LOCAL_COLLAR_REVIEW. Date: 2026-10-25.
**Mathematical verdict: PASS. Export-gate verdict: PASS.**
No unresolved mathematical objection. This review covers the complete
1077-line candidate, including its raw adapter, all-behavior consumer and
complete separating calibration, at SHA256:

`55edc0b201e0b3451a5c35b562097ba54b9e14879ec918af58fb0170a3ce4941`.

Intended packet: `UNORDERED_NINE_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM.md`.
This is ordinary mathematical review, not Lean verification. I did not
read another review, run Lean, edit an export or commit changes.

## Scope and strategic inputs

The literal six-pair box [1,4/3]^6 and triple box [1,2]^3 have one common
positive beta threshold, without ordering d and h. The seven specified
passive entries, singleton matrix and row0 upper bounds are exact inputs.
All other finite coordinates and signed singleton levels are free.
Their magnitudes can affect mesh sizes and horizon thresholds, not beta0.
The payoff target precedes accuracy; deviations include every behavioral
replacement and Never, with independent private randomization throughout.

Every required strategic object is produced: analytic or obstacle graph,
physical roots at every depth, passive guard, axis, macro, return, finite
periodic profiles and deviation bounds. No continuation, tail certificate,
return root or strategic selection remains assumed. Separate choices on
the two closed halves suffice; cross-half graph agreement or parameter
continuity is neither established nor needed.

## Ordered analytic core

I checked the input/output equations, characteristic polynomial, unique
negative root and normal. The identity for p(-r) traps r between a and k,
so 1<=r<=4/3. The remaining block has positive real parts; simplicity and
compactness give uniform spectral coordinates and graph-transform bounds.
The quadratic holomorphic transform contracts on a common radius without
requiring negative-eigenvalue modulus dominance.

The exact d=h solo1 axis forces the ordered graph's axis remainder to
carry d-h. Comparing with the exact physical threshold therefore works
uniformly as the contact sector shrinks. The positive u margin is at
least 1/24 at the linear level. This proves physicality on the full small
quadrant, including its axes. On the pair surface, the quiet2 guard is
(h-d)y-(e-b/3)w+C_pair*y*w. Since e-b/3>=5/9 and C_pair is bounded,
it is nonpositive on d>=h after shrinking the common radius. Consequently
T>=tcrit>=Psi; this lower bound is supplied rather than presumed.

## Crossed obstacle core and its boundary

I independently checked the negative right vector, the coordinate change,
the matrix A and the exact identity for f0(A s). The term
-(h-d)(3h-2b)Y/8 has the required sign, with 3h-2b>=1/3.
The fixed norm |Y|+2|W| gives ||A||<=71/72<1<=r. This is a uniform
margin, including h=d, and does not use a parameter-dependent norm.

The critical-height equation is transverse. Its exact contact identity
K_beta(s,0)=b_beta(s)f_beta(s) is crucial and valid. At h=d the full
Y-axis is preserved exactly. Analytic divisibility and vanishing leading
remainder jets give the displayed weighted errors in W+(h-d)Y+|z|.
Thus the active-wedge estimates do not lose control as h-d tends to zero.
The dissipation bound, positive successor coordinates and forward norm
contraction hold on the whole active region used by the transform.

For tau=1/1000 and L=17/16, I checked the scalar residual signs, its
strict downward slope and the upper-height invariant. The relaxed gradient
rectangle has strict margins: the Y bounds improve by the factor 7/8,
and the W upper bound by 71/72. Its lower bound
65/2304-2*(71/72)*tau is positive. The successor map is locally invertible,
justifying the almost-everywhere chain rule for Lipschitz candidates.
Zero extension across contact preserves the class. The weighted fixed-point
contraction is uniformly below one on the entire crossed closed half.

The outer physical inversion has slope above 1/2 and a nonpositive initial
residual, giving one nonnegative root for every small u,v>=0. The stopped
set is precisely the legal pair region. Its ratio contracts uniformly,
and the exact pair guard preserves legality even at h=d and the zero-axis
faces. Exact contact gluing supplies continuous selected roots. The graph
has T>=Psi and common O(beta) outer contraction at every continuation.

The passive0 continuation has a fixed positive margin. Its forced-Quit
bound uses only the row0 upper bounds, while summable hazards yield the
axis estimate p+O((1+|p|)(u+v)). On the fixed positive p interval needed
later this is uniform. Unbounded unqueried rewards cannot enter that step.

## Raw macro, return and unrestricted consumer

The maximum of the zero-v and zero-alpha solutions produces complementary
nonnegative v,alpha at positive beta. The pair chart with spectator slack
joins exactly at z=0. I checked the general singleton-flow formulas and
their nonnegative endpoint segments, including omission of flow3 at alpha0.
The projected axis in Return is well-defined off the graph-entry locus;
it becomes the actual axis when Entry vanishes.

The limiting direct and diffuse return arms join with the stated transverse
signs. Their polynomial factorizations and exact interval certificates
give a thin physical ribbon. The clipped direction chi<=8z preserves z>=0
near the pair junction. Both branches have a strictly negative transverse
return derivative at the other junction, so no global return-root choice
or differentiability of the produced axis is required.

The generic endpoint argument uses Sigma=4C+1 and F_i<=2 to give Entry>=1
at the pair face, without assuming a homogeneous graph limit. At the other
face the exact strict bound is
2D-U/3-V=-18634684506317/1486573974000000.
Uniform O(beta) axis and macro errors preserve all four face signs.
Miranda applied to (-Entry,-Return) has the correct orientation and supplies
an actual entrance and return. Passive0's macro margins are strict as stated.

The periodic construction fixes the target before truncation and meshing.
Every deviator faces opponent absorption at least x per word. Mesh error
is charged once at quitting; seam error sums over at most 1/x expected
visits. This proves regret C*max(delta)+2E_N/x and delivery error E_N/x
for complete stopping laws and Never. The uniform expected absorption-time
bound L/x gives the stated finite-horizon comparison. Signed own levels
cancel only after sure absorption has been proved. Free finite pair rewards
enter the mesh constant, which leaves the common beta threshold intact.

## Nonredundancy and adversarial boundary tests

The complete table with Z1(123)=2e and Z3(13)=(1+theta)e, 0<theta<=1/3,
belongs to the new box for small e. It violates d>=h strictly. The exact
role census leaves only the identity, and the literal singleton matrix
fixes positive row scalings, so alternative selections cannot restore order.
Unequal row1 entries also exclude every compared homogeneous-core family.

I recomputed the added Q3 term exactly from coalition probabilities and
checked the tangent t=u/2+3v/(3+theta). Its negative physical hazard on the
u=0 axis falsifies the tempting pure-triple continuation, while the hybrid
construction repairs it. This is a producer boundary test, not a UE failure.

The new Q3 term vanishes on every sure face where row3 is used. The remaining
sure-face equations and feasible punishment-tail bound are exhaustive.
For stationary supports the extra E3 term is nonnegative and bounded by
the already allowed 2e*D3^2; the complete support contradiction remains valid.
The all-weight inequalities and all fourteen child obstructions also remain
valid. In child123, q2=1 prevents querying the changed pair13 entry; in
child023 that entry is absent. Sure13 remains a child equilibrium.

The singleton matrix is unchanged, so the principal-minor, inverse-row,
degree, matching and quotient censuses retain their exact full-selection
meaning. The comparison explicitly distinguishes the all-child-profile
consumer from hypothetical methods selecting specially favorable profiles.
It does not mistake stationary nonexistence for an unrestricted gap.

## Source and export gate

I checked the cited actual declarations for rectangular Miranda, singleton
flow execution and terminal-to-uniform selection, and the punishment-vector,
protected-leaver, withdrawal/future-join and raw inverse criteria. Their
hypotheses and semantic scope match the proof and complete-selection tests.
All eight cited Lean source paths are tracked. The packet has no dependency
on another conference packet, scratch program or deferred local lemma.

The theorem is a self-contained raw-table existence class with its complete
producer and all-behavior consumer. The exact calibration proves additional
counterexample-class exclusion beyond the ordered box and compared accepted
criteria. Its positive, switching and failed-triple boundary tests are
explicit. The proposed formalization separates algebra, graph production,
common-zero production and behavioral execution without encoding strategic
existence as an assumed structure field. These facts satisfy the export gate.
The new mathematics is not claimed as checked Lean, and Fin4 remains open.
