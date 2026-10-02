# Polynomial forward certificates without punishment-floor inputs

Authors: CODEX_FRECHET_CYCLE (analytic separator and finite sure-root
characterization), CODEX_RENY (finite burn-in and floor-free composition),
and CODEX_HILBERT (stationary and sequential necessity adapters). The finite
burn-in formulation also incorporates ROOT's finite-block observation.

Independent proof reviews:

- [HILBERT: analytic separator](../feedback/CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR__BY_CODEX_HILBERT.md)
  and [RENY: analytic separator](../feedback/CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR__BY_CODEX_RENY.md);
- [HILBERT: finite burn-in](../feedback/CODEX_RENY__FINITE_FORWARD_PUNISHMENT_FLOOR_BURN_IN__BY_CODEX_HILBERT.md)
  and [HILBERT: floor-free composition](../feedback/CODEX_RENY__PUNISHMENT_FREE_POLYNOMIAL_FORWARD_CERTIFICATE__BY_CODEX_HILBERT.md);
- [FRECHET: necessity adapters](../feedback/CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT__BY_CODEX_FRECHET_CYCLE.md)
  and [RENY: full necessity/sure-root composition](../feedback/CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT__BY_CODEX_RENY.md).

The new results below are ordinary mathematics. Named existing production
declarations are distinguished explicitly from the new proofs. Frozen
original proof identities are recorded in Section 10.

## 1. Exact statement

There are four players I={0,1,2,3}, independent behavioral Quit/Continue
randomizations, rewards r(S)∈ℝ⁴ for every nonempty quitting coalition,
and zero payoff on Never. Fix M>0 with |r_i(S)|≤M. All strategic caps,
punishments and equilibria use unrestricted behavioral deviations, including
Never and arbitrarily late finite quitting dates. Equivalently these are
independent stopping laws on ℕ∪{Never}, with unilateral replacement of one
complete law. Let

    P_i = inf_[independent opponent laws] sup_[own laws] U_i,
    s_i = r_i({i}).

Here U is terminal expected reward. Thus −M≤P_i≤M. No punishment
infimum is assumed attained, and P need not be the payoff vector of any
joint profile. Punishment normality means P_i≤s_i for every i.

For a product root q∈[0,1]⁴, let c(q)=∏_i(1−q_i), a(q)=1−c(q),
F(q,v) be the Bellman successor of continuation annotation v, and e_i(q,v)
its ordinary root regret, as defined in Section 2. For B≥M and δ>0,
define the FLOOR-FREE relation ℛ_δ(B) by ALL triples (v,q,w) with

    v,w∈[−B,B]⁴,
    |w−F(q,v)|∞≤δ a(q),
    e_i(q,v)≤δ a(q)                         for every i.       (FF)

Its edge charge is a(q). Let Cap⁰_δ(B) be the supremum of total charge
over ALL finite free-start paths of these edges, allowing length zero at
every source. No feasibility as actual strategic payoffs, prescribed start,
selected component, support schedule, or lower absorption bound is imposed.

**Analytic separator theorem.** For B≥M and 0<ε≤1,

    Cap⁰_ε(B+1)<∞
      ⇒ ∃ H∈ℚ[X₀,X₁,X₂,X₃],
           H(v)−H(w)≥a(q) for EVERY (v,q,w)∈ℛ_(ε/4)(B).   (A)

Conversely, any bounded function with this inequality on ℛ_δ(B) bounds
all its finite free-start charges by sup H−inf H on the box. The analytic
theorem requires neither normality nor a positive singleton. It also holds
if the outer and inner relations respectively impose endpoint floors
v,w≥P−ε and v,w≥P−ε/4.

Write EP(B), respectively WP(B), for exact support-approximate, respectively
absorption-weighted, finite forward packets in one fixed box [−B,B]⁴,
at EVERY positive accuracy and EVERY finite requested charge, with their
prescribed punishment floors. Write EP⁰(B), WP⁰(B) when only those floors
are omitted. Their complete definitions are in Section 2.

**Input-removal theorem.** Under punishment normality, for EACH fixed B≥M,

    EP⁰(B) ⇔ EP(B),              WP⁰(B) ⇔ WP(B).            (B)

The box is unchanged. A fixed number of initial CONSTRUCTION rows is
deleted; this number depends on the table bound, box and requested accuracy,
but not on the requested surviving charge. No initial floor, actual-tail
realization, or approximate equilibrium is a producer input.

Let UE mean existence of one fixed uniform-equilibrium payoff: the payoff
is chosen before the accuracy; at every accuracy a behavioral profile and
a finite threshold control payoff approximation and every unilateral
deviation at all longer finite horizons. Define the finite sure-root
certificate

    C_sure : ∃k∈I, q∈[0,1]⁴,
                   q_k=1 and e_i(q,P)=0 for every i.       (C)

**Fixed-box normal-game characterization.** Assume normality and s_j>0
for at least one j. Put B=M+2. Then

    no UE
      ⇔ ¬C_sure and ∃δ∈ℚ, 0<δ≤1/4,
           ∃H∈ℚ[X₀,X₁,X₂,X₃],
             ∀(v,q,w)∈ℛ_δ(B), H(v)−H(w)≥a(q).            (D)

Thus H has four payoff variables, while its all-edge inequalities quantify
v,w,q and contain no P. Normality and C_sure still refer to the exact semantic P. There is no claim
to compute P, bound polynomial degree, decide a table algorithmically, or
construct a feasible negative certificate. In particular, (D) proves
neither universal UE existence nor a positive-gap example.

## 2. Definitions, indexing, and existing semantic inputs

### 2.1 Root quantities

Let p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i). For player i put

    α_i(q)=∏_(j≠i)(1−q_j),
    Q_i(q)=Σ_[T⊆I\{i}] p_(q,−i)(T) r_i(T∪{i}),
    A_i(q)=Σ_[∅≠T⊆I\{i}] p_(q,−i)(T) r_i(T),
    C_i(q,v)=A_i(q)+α_i(q)v_i,
    R(q)=Σ_[S≠∅]p_q(S)r(S),
    F(q,v)=R(q)+c(q)v,
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

In particular |R_i(q)|≤M a(q), c=(1−q_i)α_i, and
F_i=q_iQ_i+(1−q_i)C_i. Hence e_i≥0 and it is ordinary mixed-root
regret, not a full-behavior cap at an arbitrary supplied tail.

### 2.2 Forward packets and their quantifiers

An exact support-δ packet consists of H≥0, values v₀,…,v_H in the box,
and product roots q₀,…,q_(H−1), with

    v_(t+1)=F(q_t,v_t)                            (t<H),
    max(Q_i,C_i)−Q_i≤δ if q_t(i)>0,
    max(Q_i,C_i)−C_i≤δ if q_t(i)<1,               (t<H, all i),
    v_t(i)≥P_i−δ                                 (t≤H, all i).

Its charge is Σ_(t<H)a(q_t). EP(B) says such a packet exists for every
δ>0 and every requested charge Q≥0 with charge at least Q. EP⁰(B)
omits exactly the last inequalities. WP(B) uses (FF) at every row and
the endpoint floors v_t≥P−δ; WP⁰(B) uses only (FF). Equivalently,
WP⁰(B) says Cap⁰_δ(B)=∞ for every δ>0.

Construction runs from a continuation to its prefixed successor. If a
finite packet is played, chronological order is reversed. Deleting initial
construction rows does not mean deleting an initial chronological prefix,
and requires no new reattachment. A packet's abstract values need not be
literal terminal tails. Packets may vary independently with both parameters.

### 2.3 Checked inputs and the scope of self-containment

The root/cap estimates, new analytic argument, burn-in, and necessity
adapters are proved below. The following broader semantic results are
existing production inputs, not new conclusions or deferred research lemmas:

1. Exact finite forward packets in a fixed compact box imply UE.
   Weighted packets in a reward-containing box repair to exact packets in
   that SAME box. Exact packets in radius B translate to weighted packets
   in radius B+2. Thus existence in SOME fixed box is equivalent for EP
   and WP. This is not asserted to give EP(B)⇔WP(B) at identical B.
2. UE is equivalent to actual terminal approximate Nash profiles at every
   positive error, with full behavioral deviations and no fixed terminal
   target required in that premise.
3. This all-errors terminal premise implies ONE fixed AKRS alternative:
   S.1 stationary approximate equilibria at every error; S.2 instant
   sure-quitter approximate equilibria with a punishment tail; or S.3
   initially absorbing sequences whose every row is perfect up to the
   stated error against its own literal restarted terminal payoff.
4. For a row-η-perfect literal sequence, positive survival after a finite
   restart forces s_i≤η for every player. Hence a positive singleton
   forces every-restart termination when η is sufficiently small.
5. Against stationary opponents with α_i<1 the unrestricted cap is
   max(Q_i,A_i/(1−α_i)); it is at least P_i. The root Q_i and Never
   endpoint suffice because the payoff of Quit at each finite date
   interpolates these two endpoints. If α_i=1, A_i=0 and the endpoints
   are Q_i=s_i and the zero Never payoff.

Their exact declaration names and files are in Section 9. No converse to
S.3 from the paper is used, and no bounded-response restriction is imported.

## 3. Finite burn-in creates every retained punishment floor

This proof works for any nonempty finite player set. Assume normality and
|r_i(S)|≤M. Fix B≥M, τ>0 and

    0≤ζ≤min(τ/2,τ²/(8M)),       κ=τ²/(8M).

Choose an integer L≥1 with Lκ>M+B. Suppose v₀,…,v_H∈[−B,B]^I and
roots q_t satisfy only the endpoint inequalities

    Q_i(q_t)≤v_(t+1)(i)+ζ,
    C_i(q_t,v_t)≤v_(t+1)(i)+ζ.                       (E)

Then v_j≥P−τ for every L≤j≤H.

To prove this, fix a violating coordinate at a row output j≥1 and write
d_j=P_i−v_j(i)>τ, α=α_i(q_(j−1)), A=A_i(q_(j−1)). The Quit
endpoint equals s_i when all opponents Continue, and differs from s_i by
at most 2M on the remaining event. Thus normality and (E) give

    P_i−2M(1−α)≤s_i−2M(1−α)≤Q_i≤P_i−d_j+ζ.

It follows that 1−α≥(d_j−ζ)/(2M)>τ/(4M), so α<1, and Q_i<P_i.
The stationary-opponent cap max(Q_i,A/(1−α))≥P_i therefore forces
A≥(1−α)P_i. The Continue inequality in (E) now gives

    α d_(j−1)≥d_j−ζ>0.

This also proves α>0 before any division. Consequently

    d_(j−1)−d_j
      ≥[(1−α)d_j−ζ]/α
      >τ²/(4M)−ζ≥κ.                                  (G)

The numerator is positive, justifying the comparison after division by
α≤1. The same coordinate remains violating at the preceding construction
date. Iterating (G) from any j≥L yields d₀>d_j+jκ>jκ≥Lκ>M+B,
contrary to d₀≤P_i+B≤M+B. This proves every claimed floor. The cases
α=0 and α=1 were excluded by the violation itself; no hidden positive
opponent absorption assumption is needed.

For an exact support-e packet, convexity of the row payoff gives ordinary
regret at most e, so (E) holds with ζ=e. For a floor-free weighted
e-packet, each pure endpoint is at most

    F_i(q_t,v_t)+e a(q_t)≤v_(t+1)(i)+2e a(q_t)
                                      ≤v_(t+1)(i)+2e.

Thus (E) holds with ζ=2e. To produce a target accuracy δ>0 packet,
take τ=δ and choose respectively

    0<e≤min(δ,δ/2,δ²/(8M))             for EP⁰,
    0<e≤min(δ,δ/4,δ²/(16M))            for WP⁰.

Fix L as above and request original charge Q+L. Since each row has charge
at most one, H≥L. Keep v_L,…,v_H and q_L,…,q_(H−1). At most L
charge is deleted, and ALL retained endpoints, including both ends, now
have their target floors. Bellman and local-error inequalities are unchanged
and e≤δ. The box has not grown. This proves the nontrivial directions in
(B); forgetting floors proves the other directions.

No packet, equilibrium, or unbounded capacity is constructed from the reward
table in this step. It removes one input from any all-accuracy/all-charge
producer. The amount deleted is fixed before Q, which is the essential
quantifier rather than a per-word survival assertion.

## 4. Finite robust capacity produces a polynomial on all edges

We prove (A) first for the floor-free relation. In parallel, if desired,
use the nested domains K_t(b)={v∈[−b,b]⁴:v≥P−t}. Every step below
also proves the floor-bearing variant; its extra boundary check is explicit.

### 4.1 Absorption-relative common upward translation

Let h≥0 coordinatewise and |h|∞≤t. Keeping q fixed,

    F(q,v+h)=F(q,v)+c h,
    (w+h)−F(q,v+h)=(w−F(q,v))+a h.                    (T1)

The two pure-action gains change exactly by

    Q_i−F_i(q,v+h)=Q_i−F_i(q,v)−c h_i,
    C_i(q,v+h)−F_i(q,v+h)
       =C_i(q,v)−F_i(q,v)+(α_i−c)h_i.                 (T2)

Since α_i−c=q_iα_i≤a, it follows that

    e_i(q,v+h)≤e_i(q,v)+a t.                          (T3)

Every inner ℛ_(ε/4)(B) edge, shifted by ANY h∈[0,ε/4]⁴, is therefore
an outer ℛ_ε(B+1) edge. Its residual and regret are in fact at most
(ε/2)a, and its values lie between −B and B+ε/4. In the floor-bearing
case the inner floors improve under this translation and imply the weaker
outer floors. This covers the entire inner relation, not selected roots.

### 4.2 The bounded capacity-to-go is Borel

Let K be the outer compact domain, either [−B−1,B+1]⁴ or K_ε(B+1).
For x∈K let Φ_n(x) be the maximum charge over outer paths starting at x
of length at most n. For each fixed length l≤n, path constraints form a
closed subset of a finite product of K and root cubes. The finite disjoint
union over l handles all lengths ≤n. The length-zero path makes every
source fiber nonempty, even if that source admits no outgoing edge. These
compact fibers and continuity of charge prove that Φ_n is defined and
attains its maximum.

Each Φ_n is upper semicontinuous. If x_m→x, pass to a subsequence
realizing the limsup, select maximizing paths, pass to a fixed length and
then a convergent path subsequence. The limit starts at x, remains feasible
by closedness, and has the limiting charge. Hence limsup Φ_n(x_m)≤Φ_n(x).

Set Φ(x)=sup_n Φ_n(x). It is Borel as a countable supremum of Borel
functions. Finite total capacity gives 0≤Φ≤C for some C<∞. For every
outer edge (x,q,y), concatenate that edge with any finite path from y:

    Φ(x)≥a(q)+Φ(y).                                    (V)

No attainment of the all-length supremum is asserted. In particular Φ
need not be upper semicontinuous or continuous. Empty paths and free starts
are indispensable to this bounded Borel construction.

### 4.3 One-sided smoothing on a neighborhood of the inner domain

Choose a nonnegative smooth compactly supported probability density ρ
with support inside (0,ε/4)⁴. Extend Φ by zero outside the closed outer
domain to a bounded compact-support Borel function Φ̃. Define

    V(v)=∫_(ℝ⁴)ρ(h)Φ̃(v+h)dh.

Differentiating the smooth kernel, rather than the Borel function, proves
V is smooth on all of ℝ⁴.

The extension creates no fake capacity in the needed inequalities. If x
is within ε/16 in sup distance of the inner domain and h∈supp ρ, then

    −B−ε/16 < x_i+h_i < B+5ε/16.

These bounds are inside the outer box since ε≤1. In the floor-bearing
case additionally x_i+h_i>P_i−5ε/16≥P_i−ε. Thus throughout a
neighborhood of every inner boundary face, all sampled points use the
actual outer capacity. For any inner edge, (T1)–(T3) make the translated
edge admissible for every h in the support. Integrating (V) gives

    V(v)−V(w)≥a(q).                                    (S)

There is one smooth V for ALL inner endpoints and roots, including roots
with arbitrarily small positive absorption.

### 4.4 C¹ approximation retains the charge, unlike C⁰ approximation

Put D=M+B+ε/4>0. Every inner edge satisfies

    |w−v|∞≤|R(q)−a(q)v|∞+|w−F(q,v)|∞≤D a(q).          (MOVE)

There is a polynomial p with rational coefficients such that on the whole
cube [−B,B]⁴,

    sup_x Σ_i|∂_ip(x)−∂_iV(x)|≤1/(2D).                 (C1)

Here is a direct justification of the approximation used. Rescale the cube
to [0,1]⁴ and apply tensor Bernstein polynomials to the smooth function.
The derivative in coordinate i is an average with nonnegative binomial
weights of the differences n[f((k+e_i)/n)−f(k/n)]. Each such difference
is the average of ∂_if along its grid segment. Uniform continuity of that
derivative and uniformly vanishing binomial variance prove uniform
convergence of the derivative averages. This holds simultaneously for the
four derivatives, and rescaling back gives approximation in their summed
uniform norm. First obtain a strict margin in (C1). Perturb the finitely
many coefficients to rationals sufficiently little; continuity of the
coefficient-to-C¹ norm on a fixed cube preserves (C1).

The segment from v to w stays in the cube. The fundamental theorem of
calculus, (C1) and (MOVE) give

    |(p−V)(v)−(p−V)(w)|≤|v−w|∞/(2D)≤a(q)/2.

Combining with (S) yields p(v)−p(w)≥a(q)/2. Take H=2p to obtain (A).
When a(q)=0, the residual condition forces w=v, so this argument still
applies without division by the charge.

A mere uniform C⁰ error would be an absolute endpoint error, uncontrolled
relative to arbitrarily small a. The C¹ step multiplies its error by the
actual edge displacement and is therefore essential.

### 4.5 Converse and scope of the analytic theorem

Summing the drift inequality on a finite path telescopes to

    Σ_t a(q_t)≤H(v₀)−H(v_H)≤sup_K H−inf_K H.

This formulation also covers bounded functions whose extreme values are
not attained. For a polynomial on the compact domain the supremum and
infimum are attained. The bound holds over all starts and all lengths.

Bounded EXACT-Nash capacity alone is not the hypothesis. We require
bounded capacity for the entire robust outer relation, shrink its tolerance,
and reserve outer-box room. No regularity of the original all-horizon
capacity is inferred. This completes the analytic theorem.

## 5. Necessity adapters and the finite sure-root alternative

This section proves the ordinary adapters needed for the fixed box in (D).
It keeps the checked forward trichotomy separate from any unsupported
reverse-S.3 theorem.

### 5.1 Literal S.2 is exactly C_sure

The production definition of S.2, at every ε>0, supplies a sure root
quitter k, root q, and a constant punishment row from the next date onward,
with the exposed owner's stationary full cap at most P_k+ε, such that
the whole profile is terminal ε-Nash. Its checked profile-punishment
equivalence allows an arbitrary independent punishment tail instead. It
does NOT say that the first root is pure singleton or that it repeats.

For necessity take ε_n↓0 and such profiles q_n::τ_n. After a subsequence
the sure label is fixed, q_n→q, and q_k=1. Prescribed absorption at the
first root gives U_n=F(q_n,P), independently of the punishment tail. For
i≠k, the sure k screens every deviation from the tail, so its full cap
is the larger root endpoint against P. For k, its Continue cap is

    A_k(q_n)+α_k(q_n)Cap_k(τ_n)≥C_k(q_n,P),

because every opponent profile's full cap is at least P_k. Full ε_n-Nash
therefore implies e_i(q_n,P)≤ε_n for every i. Pass these continuous
inequalities to the limit to get C_sure. Also
P_i≤Cap_i(q_n::τ_n)≤U_n(i)+ε_n, giving F(q,P)≥P.

For sufficiency fix (k,q) in C_sure and ε>0. By the definition of the
infimum choose independent opponents in a tail τ_ε that hold k's full
cap to at most P_k+ε; fill k's own tail law arbitrarily. The actual
profile q::τ_ε has fixed prescribed payoff U=F(q,P). For i≠k, every
deviation is screened by sure k, so the full cap is at most U_i. For k
the full cap is

    max(Q_k(q),A_k(q)+α_k(q)Cap_k(τ_ε))≤U_k+ε.

Thus there are actual terminal ε-Nash profiles at every error. The
checked constant-row/profile-punishment equivalence yields literal S.2,
and the terminal all-errors equivalence gives UE. Letting ε↓0 in
P_i≤Cap_i(q::τ_ε)≤U_i+ε also derives U≥P. No simultaneous realization
of all P_i or Nash behavior of the punishment tail was used. Neither
normality nor a positive singleton is needed in this subsection.

### 5.2 Absorbing stationary sources give WP(M+2)

Let a stationary product q with a>0 be terminal e-Nash against all complete
responses, where 0<e≤1. Its actual payoff U satisfies |U_i|≤M and
F(q,U)=U. Immediate Quit and the punishment definition give

    Q_i−U_i≤e,                    U_i≥P_i−e.

The full Never response gives the sharper Continue estimate

    C_i(q,U)−U_i≤e(1−α_i).                             (N)

Indeed if α_i<1 its payoff is A_i/(1−α_i)≤U_i+e; multiply by
1−α_i. If α_i=1, A_i=0 and C_i(q,U)=U_i, so (N) is exact.

Use the constant annotation y=U+2e·1. Its residual is

    y−F(q,y)=2e a·1.

The Continue gain is at most e(1−α_i)+2e(α_i−c)≤3e a. The Quit
gain is at most e−2ec. If this is positive, c<1/2 and a>1/2, making
the gain at most e≤2e a; otherwise it is already nonpositive. Hence
e_i(q,y)≤3e a for all i. The floor is y≥P+e and the fixed box is
[−M−2,M+2]⁴. Repeating q and y H times with Ha≥Q gives the desired
charge at tolerance 3e. No uniform lower bound on a is needed.

If s_j>0, an S.1 witness at e<s_j cannot have a=0: that would be the
all-Never profile, with player j's deviation gain s_j. Thus S.1 supplies
WP(M+2) at every requested accuracy and charge.

### 5.3 Normal every-restart S.3 sources give EP(M)

At row error η>0, let q_t be an S.3 sequence and u_t its literal terminal
payoff after restart t. Then |u_t|≤M, u_t=F(q_t,u_(t+1)), and both
pure endpoints are at most u_t+η. Each supported endpoint is at least
u_t−η, so each supported action is within 2η of the best endpoint.

We record the all-date floor proof to make this adapter independent of a
floor assumption on the source. Fix τ>0 and
η≤min(τ/2,τ²/(8M)). If at any time one coordinate has
d_t=P_i−u_t(i)>τ, the same Quit/stationary-cap argument as Section 3
gives 0<α_i(q_t)<1 and

    1−α_i(q_t)>τ/(4M),
    α_i(q_t)d_(t+1)≥d_t−η,
    d_(t+1)−d_t>τ²/(8M).

The SAME coordinate then grows by this positive amount at every later
date, contradicting d_t≤2M. Therefore u_t≥P−τ at every date.

Choose η additionally below a positive singleton s_j. The checked
null-tail result implies that this source terminates after EVERY restart.
Consequently Σ_t a(q_t)=∞. If the sum were finite, there would be only
finitely many terms above 1/2, including all sure absorption rows. On a
sufficiently late tail, −log(1−a_t)≤2a_t would give a positive infinite
survival product, contrary to every-restart termination.

For requested support error δ and charge Q, choose τ≤δ and η>0
satisfying all these inequalities and 2η≤δ. Choose H with charge at
least Q in the first H chronological rows. Reverse that finite segment:

    v_j=u_(H−j)       (0≤j≤H),
    x_j=q_(H−1−j)     (0≤j<H).

This is an exact forward packet in [−M,M]⁴, with all endpoint floors
and support error at most δ. Hence S.3⇒EP(M). The checked upward
translation of exact packets gives WP(M+2): use support error γ≤1
with 3γ below the requested weighted tolerance, translating all values
by 2γ·1. Its residual is 2γa and its ordinary regret at most 3γa.

### 5.4 The fixed-box implication actually used

The checked terminal all-errors equivalence followed by the checked
FORWARD trichotomy gives one S.1/S.2/S.3 branch from UE. Under normality
and a positive singleton, Sections 5.1–5.3 therefore prove

    UE and ¬C_sure  ⇒  WP(M+2).                         (BOX)

Together with the existing packet consumer and C_sure⇒UE, this also
proves UE iff [EP in some fixed box or C_sure], equivalently using WP.
It does not assert C_sure⇒EP or interpret every supplied sure root as a
repeatable cycle. The radius M+2 is chosen BEFORE accuracy and charge.

## 6. Proof of the floor-free fixed-box characterization

Assume normality, a positive singleton, and B=M+2.

If there is no UE, C_sure is impossible by Section 5.1. Moreover WP⁰(B+1)
would imply WP(B+1) by the same-box input removal (B), and hence UE by
the existing weighted-packet consumer. Thus WP⁰(B+1) fails. Its complete
quantifiers give some t>0 and finite Q≥0 for which no ℛ_t(B+1) path
reaches charge Q. In particular Cap⁰_t(B+1)≤Q<∞. Choose rational
0<ε≤min(1,t). The smaller relation also has finite capacity. The analytic
theorem gives δ=ε/4∈ℚ∩(0,1/4] and rational H on ALL ℛ_δ(B) edges.
This proves the forward direction in (D).

Conversely suppose ¬C_sure and the stated polynomial exist. If UE held,
(BOX) would give weighted packets in this same B at this same δ with
arbitrarily large charge. Forgetting their floors gives ℛ_δ(B) paths,
whose charges the polynomial bounds by its finite oscillation. This is a
contradiction, proving the reverse direction.

Only the negative-to-certificate direction uses input removal to remove P
from the polynomial's ALL-edge test. The positive contradiction uses the
already floor-bearing packets from the necessity adapters. No SUM-minimum
entrance, attained semantic carrier, or approximate equilibrium source is
assumed under the no-UE premise.

## 7. Boundary and falsification tests

### 7.1 Zero charge and the sign of smoothing

If q=0 then a=0, F(q,v)=v and a feasible edge must have w=v. Such an
edge is root Nash exactly when v≥s, and any proposed polynomial satisfies
its zero drift automatically. A negative translation that sends some
v_i<s_i creates positive Quit regret while a stays zero. Therefore the
common-shift argument genuinely requires h≥0; it is not an arbitrary
signed convolution invariance assertion.

### 7.2 Why burn-in cannot assert the entry floor

Take all rewards zero, P=s=0, and v₀=−B·1. A root with two sure
quitters has both endpoints zero for every player, and exact successor
v₁=0. It is an exact Nash/Bellman row even though v₀ is far below P.
Further such rows can add charge. The retained floor theorem does not
include an arbitrary initial endpoint.

Normality is essential for the local burn-in assertion. With two players,
rewards r({0})=(−1,1), r({1})=(1,−1), r({0,1})=(−1,−1), and zero
Never, one has P=(0,0): Never guarantees nonnegative payoff, while
all-Never opponents give full cap zero. But s=(−1,−1). The all-Continue
root with constant annotation (−1/2,−1/2) is exact root Nash and exact
Bellman forever, violating the P−1/4 floor at every endpoint. Its charge
is zero, so it does NOT refute an unbounded-charge producer equivalence
without normality; it refutes precisely the local floor lemma without it.

### 7.3 An exact charged cycle forbids every separator

For each nonempty S⊆I consider the canonical stress table

    r₀(S)=1+1_(2∈S) if 0∈S, and 3·1_(2∈S) otherwise;
    r_i(S)=1_(i−1∈S) if i∈S,
           3·1_(i−1∈S)−1 otherwise, for i=1,2;
    r₃(S)=0 if 3∈S, and 1 otherwise.

Here M=3 and s=(1,0,0,0). All-Never opponents give P≤s. Set
u⁰=(1,1,0,1), u¹=(1,0,1,1), u²=(2,0,0,1), and let qⁱ give only
owner i probability 1/2 to Quit. Direct substitution gives the FORWARD
cycle

    u¹ --q⁰--> u⁰ --q²--> u² --q¹--> u¹.

Each edge is exactly Bellman and has charge 1/2. The respective vectors
C−Q are (0,1/2,0,1), (1/2,0,0,1), and (0,0,1/2,1). Each owner
is indifferent and every nonowner weakly prefers its prescribed Continue,
so the roots are exact Nash. Values lie in [−3,3]⁴ and above s≥P.
They belong to both relations at every δ>0 and B≥3. Summing the
separator would give 0≥3/2, impossible for any single-valued function.
This known solved table tests all-edge scope and orientation; it supplies
no arbitrary-table producer or new equilibrium claim.

### 7.4 The supplied S.2 root need not repeat

In a canonical four-player table set all rewards of players 1,2,3 to zero.
For player 0 set r₀(S)=3 if 0,1∈S; r₀(S)=2 if 1∈S,0∉S; and
r₀(S)=1 if 1∉S. Then P=s=(1,0,0,0). The root
q=(1,1/4,0,0), followed by all Never, is exact terminal Nash, with
U=(3/2,0,0,0). For owner 0, Q₀=3/2, A₀=1/2 and α₀=3/4.
Thus Continue against P gives 5/4≤Q₀, whereas Continue against U gives
13/8>Q₀. Repeating this supplied root is not root Nash against its own
terminal payoff. The same table has another exact constant source
q=(1,1,0,0), so this is NOT a separation of C_sure from EP. It explains
why the present proof retains the explicit C_sure arm.

## 8. Conjecture-facing change and exact remaining problem

Export-eligibility basis: this is a proved reduction of a named live
producer obligation, not just a supplied-object verifier. Under normality,
that producer no longer needs any punishment-floor input. Its negative
characterization is global over ALL allowed weighted edges in one fixed
box, with sure roots still excluded separately. The added results are
ordinary mathematics; eligibility does not assert they are Lean-checked.

The live [approximate forward-packet question](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md)
asks for a fixed-box all-accuracy/all-charge producer under contrary-case
normal data. Section 3 removes EVERY-endpoint punishment-floor inequalities
from that producer's inputs without enlarging its box. The residual and
local-regret bounds must still be proportional to the SAME row's absorption;
arbitrary small absolute errors are not substituted.

The [controller/tester sign question](../questions/QUITTING_CONTROLLER_TESTER_DUALITY.md)
already has generic semantic barrier and finite negative-certificate
formulations. The new implication is not the elementary telescoping verifier:
bounded capacity of the ENTIRE robust outer relation constructs a rational
polynomial valid on ALL inner edges. Under the stated normal-game coverage
assumptions, absence of UE itself supplies this fixed four-payoff-dimensional
certificate, with the sure-root alternative excluded.

Normality and a positive singleton remain hypotheses of (D). In the live
normal contrary case they are appropriate: if all s_i≤0, all Never is
already exact terminal Nash; and C_sure gives terminal approximate Nash
at every error. Hence a positive unrestricted SUM or MAX infimum excludes
C_sure and forces a positive singleton. This observation does not produce
the missing packet under that contrary premise.

The remaining mathematical alternatives are to rule out these polynomial
certificates under ¬C_sure for all relevant tables, or exhibit a feasible
certificate for an actual positive-gap table. Neither is achieved here.
There is no numerical gap formula from H, no bound on its degree, no
executable test for semantic P or C_sure, and no claim that negative
semidecidability is new.

## 9. Source correspondence and ordinary-versus-production boundary

The source route was the maintained `docs/TOOLKIT.md` weighted-packet,
chronological AKRS-dispatch and finite counterexample-search entries, with
the associated `docs/FRONTIER.md` scope statements. The following files are
relative to the repository root; declarations were inspected under their
imports. No fresh build or Lean implementation is claimed by this packet.

### Existing production used by the proof

- `QuittingAbsorptionWeightedForwardPacket` in
  `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacket.lean`
  supplies the literal weighted finite object, including all endpoint floors.
- `HasExactFiniteForwardPackets`, `HasAbsorptionWeightedFiniteForwardPackets`,
  `hasExactFiniteForwardPackets_of_absorptionWeighted`, and
  `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
  in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`
  supply the checked quantifiers, same-box repair, and UE consumer.
- `coordinateNashDefect_upwardTranslate_le_absorption`,
  `quittingPayoffUpwardTranslate_sub_successor_eq`,
  `hasAbsorptionWeightedFiniteForwardPackets_of_exact`, and
  `exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox`
  in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`
  supply exact-to-weighted translation and the some-box equivalence.
  The CURRENT production declaration
  `hasExactFiniteForwardPackets_rewardBox_iff_exists_absorptionWeightedBox`
  in that same file further identifies existential weighted-box production
  with exact production in the supplied reward box M. Its input is
  `hasExactFiniteForwardPackets_rewardBox_of_box` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardPacketRewardBoxReduction.lean`.
  These are existing production results, not pending claims of this packet.
  They still do not assert exact-to-weighted translation preserves B;
  that translation has the literal radius B+2.
- `QuittingFiniteForwardPacket` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
  in `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
  supply the preexisting exact packet and full semantic consumer.
- `quittingRootCoordinateNashDefect` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`, together with
  `quittingRootQuitPayoff_continuation_invariant` and
  `quittingRootContinuePayoff_update_add` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, fix root
  conventions and the coordinate continuation dependence.
- `quittingBestReplyValue_stationary`,
  `quittingStationaryUnilateralCap_eq_max_div`, and
  `quittingPunishmentValue_le_stationaryUnilateralCap` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` supply the full
  stationary opponent cap and its semantic punishment comparison.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the target-free terminal/UE existence equivalence used in Section 5.
- `QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`
  in `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumForwardTrichotomy.lean`
  supplies the FORWARD disjunction. Literal branches and row perfection
  are defined in `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`.
- `supportApproxNash_of_quittingRowεPerfect` in
  `UniformEquilibrium/Quitting/Classification/Existence/WellSupportedAbsorbingSequence.lean`
  and `quittingSingletonReward_le_error_of_positiveRestartSurvival` in
  `UniformEquilibrium/Quitting/Classification/Existence/SequentiallyPerfectAbsorbingNullTailAlternative.lean`
  supply the factor-two support comparison and every-restart implication.
- `quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment`
  in `UniformEquilibrium/Quitting/Classification/InstantPunishmentEquivalence.lean`
  relates arbitrary punishment tails to the literal constant-row S.2 form.
  `exists_oneStagePunishedProfile_of_rational_support_sureQuitter` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`
  already supplies the sure-quitter sufficiency compiler. Its rationality
  predicate, defined in `SuppliedCorrespondence.lean` in the same directory,
  means P_i−η≤tail_i, not rational coordinates or joint realizability.

### Nearest existing results and the genuinely additional claims

The exact one-step punishment amplification is already
`quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge` in
`UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`.
The rowwise opponent-absorption estimate appears as
`opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational`
in `UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`.
The summable exact-spine floor result in
`UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`
and anchored finite-prefix floor results in `PunishmentFloorFinitePrefix.lean`
do not state the approximate finite fixed-burn-in input removal proved here.

Bounded-capacity potentials already appear as
`quittingFullBoxExactPredecessor_hasFiniteBudget_of_boundedHazardCapacity`
and `quittingFullBoxExactPredecessor_value_isBoundedPotential_of_boundedHazardCapacity`
in `UniformEquilibrium/Quitting/Bellman/Finite/FullBoxExactPredecessorAbsorptionBudget.lean`.
The exact finite-horizon USC/all-horizon discontinuity distinction is also
recorded in the existing SPINOZA delayed-escape note. We do not claim Φ
becomes continuous. The new regularization constructs a DIFFERENT smooth
potential and then a rational polynomial after a controlled loss of box
and tolerance, retaining inequalities at arbitrarily small charge.

The existing `QuittingControllerUpperSemicontinuousBarrier` and
`quittingControllerTesterValue_functionBarrierDuality` in
`UniformEquilibrium/Quitting/ControllerTester/FunctionBarrierDuality.lean`
use full independent payoff/cap coordinates and all semantic root prefixes.
The present four-payoff-variable polynomial relation instead imposes robust
Bellman/root-Nash inequalities; it is not silently substituted into that API.

Existing Research declarations
`exists_finFourExactScaleStep_lower_of_infimum_pos` in
`Research/Quitting/FinFourExactScaleResolution.lean` and
`exists_finFourFixedTableCounterexampleStep_of_infimum_pos` in
`Research/Quitting/FinFourFixedTableCounterexampleSearch.lean` already give
complete finite negative certificates for their normalized rational-table
inputs. This packet claims a new certificate LANGUAGE and genuine producer
input removal, not the first counterexample semidecision, a degree bound,
or an algorithmic advantage over those declarations.

The AKRS paper [Absorption paths and equilibria in quitting games](https://link.springer.com/article/10.1007/s10107-022-01807-6)
is used only through the faithful branch definitions and the checked forward
Theorem 3.4 declaration above. Its purported quantitative reverse-S.3
Theorem 3.5 is not a proof input; the project records its failure under the
project semantics in `Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`.
The new necessity adapters have their proofs here, rather than citing that
reverse paper claim.

## 10. Frozen proof provenance and Lean handoff

This assembly leaves all original proofs unchanged:

- `CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR.md`:
  `0bef325a34314ffc7e81ab4251c4dfb622ffecff17eaacc426b868f37b4ee2c6`;
- `CODEX_RENY__FINITE_FORWARD_PUNISHMENT_FLOOR_BURN_IN.md`:
  `8b88941767cc9278725140d1e02e3dc14771e95ac75b942b65efd2178876066f`;
- `CODEX_RENY__PUNISHMENT_FREE_POLYNOMIAL_FORWARD_CERTIFICATE.md`:
  `3b4139751b4c342fa650ab72f02fa79c934c3ca7772ec0783f31545b847aa053`;
- `CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md`:
  `b9c9096f87bdd676f2cc94190a16ef35e2dcdbec6b6534c0d4f7c8303f573bda`;
- `CODEX_HILBERT__NORMAL_EQUILIBRIUM_FORWARD_OR_SURE_ROOT.md`:
  `2f4675b83684dbc1525b90c86c2de97c6bd0c60b78eb4d3da066ca45884d02ea`;
- `CODEX_FRECHET_CYCLE__AGKRS_S2_FORWARD_PACKET_SOURCE_TEST.md`:
  `b947425076715ab4bf29832b9bd586b60ca2ab4bc0b6767b82d4425a45c100b0`.

The only correction to a reviewed mathematical statement is writing
sup H−inf H for the converse with an arbitrary bounded function; polynomial
extrema on the compact domain are attained. The presentation integrates the
reviewed floor-free composition and necessity adapters, without assuming a
new producer or adding an algorithmic conclusion. FRECHET's necessity review
was not an independent review of his own S.2 proof; RENY's complete review
independently checked that dependency and the two HILBERT adapters.

A formalization handoff should separate the following finite or analytic
lemmas, retaining the exact hypotheses proved above:

1. Endpoint-error finite burn-in, followed by fixed-box EP⁰/WP⁰ input
   removal using deletion of L construction rows and the charge bound L.
2. Free-start robust path capacity with length-zero fibers, finite-horizon
   USC, and bounded Borel all-horizon capacity satisfying concatenation.
3. Common positive translation of every edge, one-sided convolution on an
   inner neighborhood, C¹ approximation, and the charge-scaled polynomial
   drift. The polynomial is existential; no degree or coefficients are
   inputs that already assume the conclusion.
4. Compact finite S.2 characterization and the stationary/S.3 fixed-box
   necessity adapters, using the named checked unrestricted cap, trichotomy,
   null-tail, terminal-selection and weighted-packet declarations.
5. The floor-free no-UE characterization, with C_sure excluded and fixed
   B=M+2, distinguishing its ordinary proof from all existing checked inputs.

The mathematical output is a complete global finite-dimensional certificate
language plus removal of a real producer input. The live sign and production
problem is still open. No Lean implementation or table search is supplied.
