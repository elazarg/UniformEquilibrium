# Global polynomial drift: singleton faces and the first-derivative obstruction

Owner: CODEX_HILBERT. Ordinary mathematical test, not independently reviewed
or Lean-checked. The exact facewise derivative constraint below is proved.
It recovers an already solved homogeneous matrix exclusion; the derivative
test at the singleton point cannot eliminate the invertible hard matrix
case. No new equilibrium producer or negative table is obtained.

## 1. Bounded question and full edge hypothesis

Let four players independently use complete stopping laws, with first finite
stopping coalition rewards r(S), |r_i(S)|≤M, Never zero, and own-singleton
vector s=(1,0,0,0). Thus M≥1. Set B=M+2. Canonical normality P≤s follows
from all opponents Never, but no punishment value is used in the test below.

For q∈[0,1]⁴ define c=∏_i(1−q_i), a=1−c and
F(q,v)=Σ_{S≠∅}p_q(S)r(S)+cv. Let Q_i,C_i be the two root action
payoffs against continuation v, and e_i=max(Q_i,C_i)−F_i. Assume that
for some fixed δ>0 and some polynomial H,

    H(v)−H(w)≥a(q)                                    (D)

holds for **every** triple with v,w∈[−B,B]⁴, e_i(q,v)≤δa for every
i, and ||w−F(q,v)||∞≤δa. There are no supplied endpoint floors, actual
source anchors, selected components, or restrictions to small roots in (D).

Question tested: can the common derivative restrictions forced by (D)
exclude the full-standard-Q/no-homogeneous canonical matrix residual, and
therefore force an already available equilibrium consumer?

Write Γ_{ji}=r_j({i})−s_j, so Γ has zero diagonal. A necessary condition
will be derived on entire singleton faces, not just at a minimizing point
of H. Nevertheless, reducing it to one derivative loses the needed global
information.

## 2. Exact facewise necessary inequality

Let v be strictly inside the coordinate box with

    v_i=s_i,        v_j≥s_j for every j≠i.

Then (D) forces

    ∇H(v)·(v−r({i})) ≥ 1+δ||∇H(v)||₁.                 (F)

**Proof.** First assume v_j>s_j for j≠i. Give only player i hazard
t∈(0,1). Then a=t and

    F(q,v)=v+t(r({i})−v).

The owner's two endpoints both equal s_i, so its root regret is zero.
Every other player j prescribes Continue, and its Quit-minus-Continue gap
is exactly

    (1−t)(s_j−v_j)+t[r_j({i,j})−r_j({i})].             (1)

It is strictly negative for sufficiently small t. Therefore all root
regrets vanish, regardless of the collision reward signs. Fix any
z∈[−1,1]⁴ and set

    w_t=v+t(r({i})−v+δz).

For small t this endpoint is still in the fixed box and the Bellman
residual is at most δt. Applying (D), dividing by t and taking t↓0 gives

    ∇H(v)·(v−r({i})−δz)≥1.

Choose each z_j with the sign of ∂_jH(v), obtaining (F). For coordinates
v_j=s_j, approach them from strictly above with v_i unchanged. Those
points remain in the box, and continuity of ∇H passes (F) to the limit.
The size of t may depend on the approach point; the proof does not
incorrectly require uniform small-root admissibility across this limit.

Only C¹ regularity was used. The perturbation z is a permissible change of
the abstract endpoint, not a correlated strategy or an actual payoff
perturbation. Equation (D) includes all such endpoints by hypothesis.

## 3. What the common derivative at s can and cannot exclude

Let h=∇H(s). Applying (F) for all four labels yields one common vector

    Γᵀh ≤ −(1+δ||h||₁)·1.                             (J)

Thus if z≥0, z≠0 and Γz=0, multiplication by z gives a contradiction.
This is a true table-level restriction, not four unrelated edge witnesses.

Its exact limitation is also elementary. Allow δ to be selected positively,
as the certificate characterization does. There exist h and δ>0 satisfying
(J) **if and only if** Γ has no nonzero nonnegative kernel vector.

Indeed, the absence of such a vector means that zero is outside the convex
hull of the four columns. Strict finite-dimensional separation gives h₀
with Γᵀh₀<0. Scale it so every coordinate is at most −2, then choose
δ>0 small enough that δ||h₀||₁≤1. This proves (J), while the reverse
was just shown. Equivalently, if Γ is invertible, take
h₀=−2Γ^{−T}1 and then choose a sufficiently small δ.

Consequently this first-derivative test cannot eliminate **any invertible
singleton comparison matrix** solely because it is standard Q, or because
its proper principals fail projective Q. The certificate tolerance is
existential; imposing a separate lower bound on it would change the claim.

## 4. The full face inequalities recover the known homogeneous consumer

Suppose λ lies in the probability simplex, x=Γλ≥0, and
λ_i x_i=0 for every i. This is the homogeneous singleton LCP condition.
The vector v=s+x=Σ_i λ_i r({i}) is in the reward box, hence strictly
inside the padded box. For every i with λ_i>0, v_i=s_i, so (F) applies.
Average those inequalities with weights λ_i. Their left side is

    ∇H(v)·(v−Σ_iλ_i r({i}))=0,

while their right side is 1+δ||∇H(v)||₁>0, contradiction.

This is stronger than checking only (J), since x may be nonzero. It is
not a new UE class: a full homogeneous singleton witness already feeds
the checked homogeneous-matrix equilibrium producer. The calculation
provides a direct correspondence between that known positive class and
the new polynomial negative certificate.

There is no proof that absence of a homogeneous solution guarantees a
global H satisfying (F), much less one satisfying (D). The pointwise
inequalities at different v must be derivatives of the **same** function;
discarding that compatibility is precisely the loss in the first-jet test.

## 5. Exact existing residual-matrix test

Use the already recorded signed-cycle singleton matrix

    Γ* = [ 0 −1 −1  6 ]
         [ 6  0 −1 −1 ]
         [−1  6  0 −1 ]
         [−1 −1  6  0 ].

Exact arithmetic gives

    Γ*ᵀ(−1,−1,−1,−1)ᵀ=(−4,−4,−4,−4)ᵀ,
    1200 Γ*⁻¹ = [ 37 209  13  41 ]
                 [ 41  37 209  13 ]
                 [ 13  41  37 209 ]
                 [209  13  41  37 ].

Thus h=(−1,−1,−1,−1) passes (J) for every 0<δ≤1/4. The positive
inverse proves absence of a homogeneous solution: if x=Γ*z≥0 and
z≥0 are complementary, then z=Γ*⁻¹x and
xᵀΓ*⁻¹x=zᵀx=0; positivity forces x=z=0. The same positive inverse
is strictly copositive and standard Q; swapping complementary variables
through inversion gives standard Q for Γ*. Its opposite 2×2 principal
has both off-diagonal entries −1 and fails projective Q.

These matrix facts are already proved in the signed-cycle construction,
not inferred from a finite set of right-hand-side tests. The displayed
inverse and derivative calculation were independently checked by exact
rational arithmetic here. This table is already solved by its balanced
cycle producer. It is used only to refute the implication from the
first-jet test to matrix-class exclusion, not to manufacture a negative
certificate or reopen a solved regression.

## 6. Exact source comparison and stopping point

The inspected route was the canonical normalization/source section of
`docs/FRONTIER.md`, including
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` and
`exists_finFour_no_uniformPayoff_iff_exists_singlePivot` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
These concern one literal canonical table and all behavioral deviations;
they do not transport a chosen minimum or its ancestry.

`HomogeneousMatrixBranch.full_homogeneous` and
`fullHomogeneousWitness_singletonMixture` in
`Quitting/Classification/LCP/HomogeneousProducer.lean` identify exactly
the witness consumed in Section 4. `ResidualHardClass` in
`Quitting/Classification/LCP/Gate.lean` explicitly excludes that branch;
it does not by itself give a strategic consumer. The precise matrix
definitions were checked in `MatrixClasses.lean`.

The nearby quadratic full-box/reset-rank test concerns a different semantic
barrier problem and its whole table family is already solved by a supplied
stationary consumer. No degree increase or new parameter search was used
here. The signed-cycle matrix and all-q proof are in
`CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER.md`; their role here is
only the exact limited-test falsifier above.

**Result of this bounded attack:** the singleton-face calculation is sound,
but it has not supplied a new outgoing consumer beyond the homogeneous
class. The common first derivative is inadequate even at generic invertible
matrices. The surviving question is whether compatibility of the full
facewise field (F), together with finite positive-root constraints in (D)
that retain collision rewards, forces the sure-root consumer on a
no-homogeneous/full-Q table. No such implication is currently proved.
It must not be replaced by the already known all-Continue freeze at a
minimum, a selected low-degree ansatz, or a separator on one chosen subset.
