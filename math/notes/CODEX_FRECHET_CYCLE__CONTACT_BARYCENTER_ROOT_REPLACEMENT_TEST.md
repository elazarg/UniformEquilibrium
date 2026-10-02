# Contact barycenter replacement: valid consumer, no global forcing obtained

Owner: CODEX_FRECHET_CYCLE. Bounded ordinary mathematical test, now stopped.
The convex-program consumer is correct. A short canonical example refutes
forcing from contact-local facts, even at the lower-boundary minimizer. It is
not a counterexample to the stronger hypothesis of a universal polynomial
certificate. No balanced contact replacement was produced from that full
hypothesis, and no new conjecture exclusion or export is claimed.

## 1. Exact candidate and the valid consumer

Let r be a canonical Fin4 table with own-singletons s=(1,0,0,0), zero Never,
independent root choices, and |r_i(S)|≤M. Put K=[−M−2,M+2]⁴. Write

    F(q,v)=R(q)+c(q)v,       a(q)=1−c(q),
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

Suppose H is a polynomial with unit drift on the full robust relation:
for some δ>0 and EVERY v,w∈K and product root q,

    ||w−F(q,v)||∞≤δa(q),   e_i(q,v)≤δa(q) for all i
      ⇒ H(v)−H(w)≥a(q).                              (D)

Let f=co H be its lower convex envelope over the SAME K. Suppose an
attained finite decomposition at x is

    θ_k>0,   Σ_kθ_k=1,   z^k∈K,
    Σ_kθ_k z^k=x,       Σ_kθ_k H(z^k)=f(x).           (C)

Attainment is available for continuous H on a compact box. The convex hull
of its compact graph in ℝ⁵ is compact, by the finite Carathéodory theorem;
the lowest point in the fiber over x therefore belongs to that hull and has
a finite decomposition. The argument below also works directly with any
supplied attained decomposition, without a support-size optimization.

Choose a DIFFERENT exact Nash root q^k at each contact if desired, and set
w^k=F(q^k,z^k). If

    Σ_kθ_k w^k=x,       Σ_kθ_k a(q^k)>0,              (B)

then (D) gives

    Σ_kθ_k H(w^k)
       ≤Σ_kθ_k H(z^k)−Σ_kθ_k a(q^k)<f(x).

But the new points, with the same weights, are a feasible decomposition of
x, contradicting the definition of f. This is a valid mathematical
consumer. It does not require playing a correlated lottery or compiling the
contacts as a temporal path. Extra finite mixtures of exact roots at one
contact can likewise be incorporated into the decomposition.

The unresolved producer is (B), from actual root geometry under (D), not
the convex-program inequality. Finite Nash existence at the separate z^k
does not itself say that their replacement barycenter is x.

## 2. What the universal hypothesis says at all contacts

If ℓ(v)=h·v+b is a global affine minorant of f with ℓ(x)=f(x), then
every positive-weight contact in (C) satisfies H(z^k)=ℓ(z^k). Indeed
each H(z^k)−ℓ(z^k) is nonnegative and their weighted sum is zero.
Such a supporting affine function is available, in particular, when x
is interior to K; no boundary subgradient is silently assumed.

For EVERY exact root at each such contact, the universal inequality gives

    ℓ(z^k)−ℓ(w^k)
      =H(z^k)−ℓ(w^k)
      ≥H(z^k)−H(w^k)≥a(q^k).                       (S)

Thus all positive contact replacements lie on the same strictly decreasing
side of an affine functional. Summing (S) would contradict (B) immediately.
This is genuinely an application of the universal H inequality, not a
convexification-preservation assumption. It explains why mere nonemptiness
of the individual exact-root successor sets supplies no balancing theorem.

The target remains to force (B) by some additional actual-game argument
and thereby contradict (D). Equation (S) is not declared an independent
counterexample to that target: it is what a hypothetical certificate must
obey and what a successful global forcing argument would have to defeat.

## 3. Exact failure of contact-local forcing at the proposed boundary point

The following solved canonical table is only a scope test. For every
nonempty S⊆{0,1,2,3}, set

    r_0(S)=1_(0∈S),
    r_j(S)=1_(j∉S)       for j=1,2,3.

Here M=1 and K=[−3,3]⁴ is precisely the padded reward box. P=s:
the pivot guarantees 1 by immediate Quit; the other players have
nonnegative rewards; all-Never opponents give the matching individual
upper bounds. The game already has the pure terminal equilibrium with
the pivot quitting immediately and the others continuing.

Take the rational polynomial

    H(v)=−2v_0+[v_0(v_0−2)]²
                 +10Σ_(j=1,2,3)(v_j−1)².

Let

    x=(1,1,1,1),
    z⁻=(0,1,1,1),       z⁺=(2,1,1,1).

The convex function

    g(v)=−2v_0+10Σ_(j=1,2,3)(v_j−1)²

is a global minorant of H. Thus f=co H≥g. The equal-weight contacts
z⁻,z⁺ give cost (0−4)/2=−2=g(x), so f(x)=−2.

Every attained optimal decomposition of x has exactly these contact
locations and total weight 1/2 at each. To see this, the affine term
averages to −2, while every remaining summand of H is a nonnegative
square. Equality forces each positive-weight contact to have v_0∈{0,2}
and v_j=1 for all j>0. Its barycenter then forces the two total weights.

Moreover x is the UNIQUE minimizer of f on the same lower boundary used
in the convex no-go:

    C=[1,3]×[0,3]³,
    L={v∈C : some v_i=s_i}.

On the face v_0=1, f≥g≥−2, with equality possible only at x. On any
other lower face, some v_j=0 with j>0, so f≥g≥−6+10=4>−2.

All exact roots at both contacts can be classified without a selection
assumption. At either contact, each nonpivot j has Q_j=0 and C_j=1,
regardless of other root probabilities. Exact Nash therefore forces all
three nonpivots to Continue. The pivot then has Q_0=1 and C_0=v_0.
Consequently the UNIQUE roots and successors are

    z⁻: q⁻=(1,0,0,0),   w⁻=x,    a(q⁻)=1;
    z⁺: q⁺=(0,0,0,0),   w⁺=z⁺,   a(q⁺)=0.

Even the exact H drift holds at ALL these contact roots:

    H(z⁻)−H(w⁻)=0−(−1)=1,
    H(z⁺)−H(w⁺)=0.

Yet every optimal contact decomposition has replacement barycenter

    (w⁻+w⁺)/2=(3/2,1,1,1)≠x.

Its weighted objective decreases from −2 to −5/2, but at the wrong
barycenter. This is not a contradiction to envelope optimality. Randomizing
over different exact roots cannot help, since both roots are unique.

The polynomial H is NOT a universal certificate for this table. At x,
the sure-pivot root is exact Nash and F(q,x)=x, so its global drift is
0<1. This explicit failure is essential: the example refutes only forcing
from optimal contacts, boundary minimality, finite Nash existence, and all
contact-local drift inequalities. It does not refute forcing which uses
(D) at noncontact points or elsewhere in the full box. No hard-class or
positive-gap claim is made for this solved table.

All displayed endpoints and objective values were independently checked
using exact rational arithmetic and enumeration of the eight opponent
coalitions for each root endpoint. Uniqueness rests on the formulas above,
not on finite numerical sampling.

## 4. Full drift at the noncontact boundary point: the exact remaining gap

Return to the hypothetical global certificate (D), not the example. Put
G=H−f≥0. Every admissible edge gives exactly

    G(w)≤G(v)+f(v)−f(w)−a(q).                       (A)

If v minimizes f on L, has exactly one tight singleton coordinate, and a
small solo root keeps w on L, then f(w)≥f(v), so (A) yields

    G(w)≤G(v)−a(q).

This uses the missing noncontact inequality honestly, but it is only a
bounded potential decrease. It does not keep w in argmin_L f, preserve
the contact decomposition's barycenter, or provide a new contact-return
selection at w. At a multiple-tight-coordinate point even the admissible
solo-root step needs additional root geometry. No iteration or arbitrary
charged return follows from (A) alone.

I obtained no forcing of (B) from the universal hypothesis beyond these
inequalities. The source problem is therefore still open, not disproved
by Section 3 and not solved by renaming (A) as progress. This bounded
contact-replacement test stops here.

## 5. Narrow source comparison and semantic boundary

The exact root and ordinary-regret declarations inspected were
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean` and
`quittingRootCoordinateNashDefect` in
`UniformEquilibrium/Quitting/Root/NashDefect.lean`.

The current fixed-box source interface was read directly:
`quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot`
and `hasFixedBoxPackets_of_uniformEquilibriumPayoff_of_noSureRoot` in
`UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean`.
Under Fin4 normality and a positive singleton these retain exactly the
M+2 box and the separate semantic sure-root arm. They are not arbitrary-table
packet producers. No domain or source quantifier was altered in this test.

The exact jump-image nonconvexity example in
`formalized/EXACT_ONE_JUMP_AND_PROPER_SINGLETON_FLOW_CLOSURE.md` concerns
one selected root at one continuation. The present consumer allows
different roots at different contacts and does not claim to realize their
lottery as gameplay. Thus that earlier no-go is not a refutation of this
consumer. The stopped thinning/returned-block argument likewise is not used.

No export, Lean change, or new global certificate-class restriction results
from this note. Its durable output is the valid barycenter consumer, the
exact limit of contact-local forcing, and the unresolved use of universal
nonconvex drift needed for an actual source.
