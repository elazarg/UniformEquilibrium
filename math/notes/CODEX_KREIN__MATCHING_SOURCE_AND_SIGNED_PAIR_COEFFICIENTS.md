# Matching sources and signed pair coefficients

Identity: CODEX_KREIN. Ordinary mathematics, not Lean-checked.

Status: two proved matrix reductions for the simultaneous-pair producer
under development. They are supporting mathematics with that concrete
consumer, not a separate export or a claim of arbitrary-table closure.
The existing cubic theorem in the owned all-player-clock note is unchanged.

## 1. The exact source and matching sign chamber

Let I={0,1,2,3}. Let f=(01)(23) be the favorable matching and let
a=(02)(13) be the scheduled active-pair matching. Write o=f∘a=a∘f.
Let Γ be a real matrix with zero diagonal and

    Γ_i,f(i)>0,       Γ_i,a(i)=−b_i<0,       Γ_i,o(i)<0.          (1)

No equality among the positive or negative magnitudes is imposed.
Let P be the permutation matrix of f, acting by (Px)_i=x_f(i).
Then M=ΓP has positive diagonal and nonpositive off-diagonal entries;
its two strictly negative positions in row i are a(i),o(i).
The directed graph of these negative positions is strongly connected.

For a literal quitting table, Γ_ij=r_i({j})−r_i({i}). The inspected
source
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`,
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`,
states that original-game nonexistence of a uniform-equilibrium payoff
implies textbook standard Q for this actual matrix. It has no own-singleton
sign premise, strategy hypothesis, or supplied punishment witness.
The definitions are in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean` and
`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`.
No transpose or translation of the actual Never reward is involved.

### Standard Q forces a strictly positive inverse

Apply standard Q to the offset (−1,−1,−1,−1). A complementarity solution
has z≥0, Γz−1≥0, and z_i(Γz−1)_i=0. In row i, the only positive
matrix entry is at f(i), so Γz≥1 forces z_f(i)>0. Thus all z_i>0,
complementarity gives Γz=1, and u=Pz>0 satisfies Mu=1.

Here is an elementary inverse proof, including the needed strictness.
Let D be the positive diagonal of M and C=I−D⁻¹M. Then C≥0 and

    Cu=u−D⁻¹1<u.

In the weighted sup norm ‖x‖_u=max_i |x_i|/u_i, the operator norm
of C is at most ρ=max_i(Cu)_i/u_i<1. Hence

    M⁻¹=(I+C+C²+⋯)D⁻¹≥0.

The negative-position graph of M is strongly connected, so for every
ordered pair (i,j), some power C^n has a positive (i,j) entry. The
series therefore makes every entry of M⁻¹ strictly positive. Finally
Γ=MP, whence Γ⁻¹=P M⁻¹>0.

This also proves M nonsingular without assuming it beforehand. Since
I−tC is nonsingular for 0≤t≤1, its determinant retains its value's
positive sign at t=0. Thus det M>0 and det Γ>0, because P consists
of two transpositions. In particular the negative-determinant inverse
exit is not the source of this deduction.

The contrapositive is useful: within (1), failure of strict inverse
positivity is an existing original-game UE exit, by the inspected
no-UE-to-Q source. A pair-phase producer that uses inverse positivity
need not retain it as an additional raw restriction on this chamber.
This statement is not a new general Q criterion outside (1).

## 2. Uniform inverse positivity with signed participant increments

Suppose Γ satisfies (1) and Γ⁻¹>0. Choose real participant increments

    Π_i>−b_i,

and put α_i=max(−Π_i,0), so 0≤α_i<b_i. For θ∈[0,1]⁴ define

    B(θ)_ij=Γ_ij+α_i θ_i 1_{j=a(i)}.                           (2)

**Claim.** Every B(θ) is invertible with strictly positive inverse,
and there are constants 0<m≤L<∞ such that

    m≤B(θ)⁻¹_ij≤L                                             (3)

for all θ and all i,j.

Indeed M(θ)=B(θ)P is a Z-matrix with the same positive diagonal
as M=ΓP. Its changed off-diagonal entry is −b_i+α_iθ_i<0,
so the negative-position graph remains strongly connected. Also
M(θ)≥M entrywise. With u=M⁻¹1>0 we obtain M(θ)u≥Mu=1.
The weighted-norm geometric-series argument from Section 1 applies
to every M(θ), yielding a strictly positive inverse. Since the coefficient
cube is compact and all its matrices remain invertible, the inverse is
continuous and its finitely many entries have a positive minimum and
a finite maximum. Multiplication by P preserves these bounds and gives
(3). This proves the uniformity on the closed cube, not just along a
postulated rate path.

One may also bound the inverses above without compactness:

    M⁻¹−M(θ)⁻¹=M⁻¹[M(θ)−M]M(θ)⁻¹≥0.

The lower bound needs the retained strict off-diagonal signs; at the
excluded boundary Π_i=−b_i an edge may disappear, so the present
argument does not silently include that boundary.

## 3. Application to the actual pair-phase equations

Partition I into A={0,2}, B={1,3}. In addition to (1), let

    s_i=r_i({i}),
    Π_i=r_i({i,a(i)})−s_i>−b_i,
    K_i=r_i({f(i),o(i)})−s_i≤0.

For positive hazard odds X_i=q_i/(1−q_i), active-phase indifference
between Quit and Continue forces the active and passive values

    U_i=s_i+Π_i q_a(i),
    W_i=s_i+(Π_i+b_i)X_a(i)>s_i.                              (4)

Write j=f(i), k=o(i). The passive Continue identity, multiplied by
(1+X_j)(1+X_k), is precisely

    (Π_i+b_i)X_a(i)(1+X_j)(1+X_k)
      =Γ_ij X_j+Γ_ik X_k+K_iX_jX_k
        +Π_i X_a(i)/(1+X_a(i)).                              (5)

Equivalently ΓX=N(X), where

    N_i(X)=(Π_i+b_i)X_a(i)[(1+X_j)(1+X_k)−1]
            +Π_i X_a(i)²/(1+X_a(i))−K_i X_jX_k.

The second term can be negative. It cannot simply be discarded in a
nonnegative-cone argument. Instead take θ_i=X_a(i)/(1+X_a(i))
in (2) and move exactly that negative part to the left. Equation (5)
is then equivalent to

    B(θ(X))X=N⁺(X),

    N⁺_i(X)=(Π_i+b_i)X_a(i)[(1+X_j)(1+X_k)−1]
              +max(Π_i,0)X_a(i)²/(1+X_a(i))−K_i X_jX_k.       (6)

All terms of N⁺ are nonnegative, and N⁺ is strictly positive when
X>0. Thus the continuous map

    F(X)=B(θ(X))⁻¹N⁺(X)

has uniformly positive normalized image by (3). Near zero it is
O(‖X‖²). On any fixed interior simplex cone X=r p, p_i≥δ>0,
its size grows at least cubically in r, from the term
(Π_i+b_i)X_a(i)X_jX_k. These are exactly the positivity, small-radius
compression and large-radius expansion premises needed by the
simplex-times-radius fixed-point selection. They now hold with
independent signed Π_i>−b_i, not only nonnegative Π_i.

The twelve raw caps

    r_i({i,j})≤s_i for j∈{f(i),o(i)},
    r_i({i,f(i),o(i)})≤s_i

still make passive Quit at most s_i, while (4) makes its Continue
value strictly above s_i. There is no new strategic consumer in this
note: the simultaneous-pair construction must still supply the positive
fixed point, the resulting proper rates, and the complete behavioral
and deleted-opponent horizon proof. The present algebra gives the
signed extension of that actual proposed producer, not a separately
assumed strategy certificate.

### Exact signed-coefficient check

Take every s_i=b_i=1, favorable singleton difference H=17/4, both
harmful differences −1, Π_i=−1/2 and K_i=−1. Let every X_i=1,
so every rate is 1/2. Then θ_i=1/2 and the changed within-pair
entry of B is −3/4. Every row of B times X is

    17/4−3/4−1=5/2.

Every N⁺ entry is (1/2)(4−1)+1=5/2. Values in (4) are
U_i=3/4 and W_i=3/2, so the active value lies below its singleton
while the passive value retains a strict floor. This checks the actual
negative-part movement and is only an algebra/semantics regression,
not a claimed new noncoverage fixture.

## 4. One branch already has a pure exit

For the common-parameter cubic class, K≥0 gives a pure active-pair
exit without any matrix hypothesis: each participant prefers the
joint reward s_i+Πb_i to leaving for s_i−b_i because Π>−1, and
every outsider's joining reward is at most s_i, whereas its passive
joint reward is s_i+Kb_i≥s_i. Opponents then absorb immediately
against every unilateral strategy, so this is an exact terminal Nash
profile with the usual live-zero O(1/N) delivery estimate.

More generally either active pair is a pure exit whenever both of
its outsiders have K_i≥0. Accordingly a future arbitrary-sign K_i
extension only needs to address the residual in which each active
pair has at least one outsider with K_i<0. No claim resolving that
mixed-sign residual is made here.

Concrete next question: incorporate (1)–(6) into the asymmetric
positive-cone producer, then test whether a sign-changing passive
increment can be handled without losing the exact outsider caps.
