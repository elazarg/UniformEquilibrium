# Bounded adversarial check of the one-positive-column producer

Reviewer: CODEX_TURING_BOX.

Frozen source: `CODEX_EMMY_BOX__ONE_POSITIVE_COLUMN_SINGLE_JACKPOT.md`,
SHA256 `16d06e04dafce92e9b223dbeb4d7127bea236fd848d1ce253fee52593bb56873`.

Scope: Sections1–5, including all finite player counts in the statement,
exact pole cancellation, determinant, compact-parameter uniformity,
scale-thick quantifiers, full unrestricted terminal Nash and the same-profile
uniform-payoff conclusion. Fixture coverage and Section6 are complementary
work; this check does not certify universal novelty or any Lean producer.

Verdict: bounded independent PASS; no mathematical objection found. I tried
to falsify the selected-pair boundary d=1, arbitrary signed other rewards,
and the growing rather than fixed perturbation box. All survive the stated
parameter order. The proof does not require an all-positive inverse.

## 1. Exact coordinate and pole accounting

For each player i, write p_i(T) for the probability of the opponent quitter
set T at one date. Direct finite-coalition enumeration gives

    Q_i=Σ[T⊆I\{i}] p_i(T) r_i(T∪{i}),
    B_i=Σ[∅≠T⊆I\{i}] p_i(T) r_i(T),
    H_i=(1−alpha_i)Q_i−B_i.

The only growing coordinate is r_a(S*) and a∈S*. It therefore appears in
Q_a, not B_a and not any other player's own payoff field. With d=|S*|−1,
t=M^(−1/d), and q=tz, its contribution to H_a/t is exactly

    A [(1−Π[j≠a](1−tz_j))/t]
        Π[j∈S*\{a}]z_j Π[j∉S*](1−tz_j).

The bracket is a polynomial, with constant term Σ[j≠a]z_j. Thus the
displayed AP(z)e_a is the exact constant coefficient, not a formal
Laurent truncation. The selected coordinate being participatory is essential.

At singleton order Q_i=s_i+O(t), while
B_i=t Σ[j≠i]r_i({j})z_j+O(t²). Hence the other constant coefficient in
H/t is −Gamma z. Every nonsingleton coefficient contributes at order at
least t² to H: if its recipient participates, its Q monomial has degree
at least one and is multiplied by 1−alpha_i; otherwise its B monomial has
degree at least two. The selected bounded residual is handled by the same
calculation. This proves the exact polynomial form(3), with no hidden sign
or omitted own singleton term.

As an independent algebraic test, I enumerated each individual coalition
coordinate in n=3,4,5, for two different recipients, and expanded it
symbolically in t. Every nonsingleton monomial had minimum degree at least
two before division, and every participatory selected pole had exactly the
stated polynomial extension and leading coefficient. These finite tests
support, rather than replace, the general degree argument above.

## 2. Positive root and rank-one determinant

Let v=Gamma^(−1)e_a>0. Positivity of P(v), homogeneity of degree d+1,
and A>0 give the explicit positive root z*=rho v, where
rho=(AP(v))^(−1/d). Indeed AP(z*)=rho and Gamma z*=rho e_a.

For J=−Gamma+A e_a(grad P(z*))ᵀ, the matrix determinant lemma gives

    det J=det(−Gamma)[1−A grad P(z*)·v].

Euler's identity and z*=rho v give A grad P(z*)·v=d+1 exactly. Therefore
det J=−d det(−Gamma) is nonzero for every permitted coalition, including
the pair case d=1. No positivity of the other inverse columns entered.

The n≥2 qualification is sufficient for the later response argument. For
n=2 the strict positive-column hypothesis on an invertible zero-diagonal
Gamma cannot actually hold; this empty input case causes no logical issue.

## 3. Uniform parameters and the scale-thick region

For a fixed bounded nonsingleton box, Phi(0,z) is independent of that box.
One can choose one small closed ball about z* in the positive orthant and
use the fixed invertible J to obtain a uniform contraction there: on a
smaller ball the derivative at t=0 is close to J, and for sufficiently
small |t| the derivative and residual changes are uniform over the compact
coefficient box. This supplies one threshold for EVERY point in that box;
it is not a separate table-dependent IFT threshold masquerading as a
uniform M0.

On a compact set of singleton/A inputs lying inside the stated open
invertibility and strict-column-positive region, z* is continuous and
uniformly interior, J is continuously invertible, and all coefficients and
inverse norms remain bounded. The same compactness/contraction argument
gives the claimed uniform threshold and bounded-data asymptotics, with
recipient and coalition fixed. No uniformity on a noncompact sign region
or as A tends to zero is asserted.

For the scale-thick box, put each nonsingleton residual coefficient b=e/t.
The ordinary nonsingleton H monomial of degree k≥2 becomes a monomial of
degree k−2≥0 in H/t. The selected residual becomes t^(d−1)e times a
polynomial. Thus the exact field is polynomial in(t,z,e) even when d=1.
In that boundary case the e term can survive at t=0; it need NOT tend to
zero for fixed nonzero e. This is harmless because the parameter IFT is
applied at(t,e)=(0,0), and then includes a fixed small e-box. Taking one
kappa inside that box gives all coefficients |b|≤kappa/t simultaneously.
Choosing kappa sufficiently small also preserves the selected positive
coefficient when d=1. The source makes no bounded-data leading-asymptotic
claim uniformly throughout this scale-thick box, correctly.

The order of quantifiers is therefore valid: for the fixed singleton/A
data choose kappa and M1 once, then allow EVERY bounded e-vector at EVERY
M>M1. Positivity and q_i<1 follow from keeping z in one positive bounded
neighborhood and taking t sufficiently small. No selected auxiliary Nash
component or strategic witness is an input to this producer.

## 4. Complete responses, Never and uniform payoffs

At an exact all-interior root H=0, each alpha_i<1 and
B_i=(1−alpha_i)Q_i. Evaluation of the stationary prescribed law gives
U_i=Q_i. At every live date, forced Quit gives U_i and Continue followed
by the displayed value also gives U_i. For a pure deadline m the exact
value is

    Σ[t<m]alpha_i^t B_i+alpha_i^m Q_i=U_i,

while Never gives B_i/(1−alpha_i)=U_i. Arbitrary signs of U_i or of any
finite reward do not affect either identity. Never is not incorrectly
assigned zero when opponents quit properly.

The unique nonabsorbed history contains only Continue actions. A complete
private behavioral replacement is therefore a distribution on first-Quit
dates and Never, independent of the opponent seeds; integrating the pure
equalities covers the entire original deviation class. Alternatively the
Bellman equality and player-deleted geometric tail yield the same result.
No public correlation, changed information or restriction to stationary
deviations is used.

For each fixed produced table, its reward bound is finite, and the time to
an opponent quit has geometric mean 1/(1−alpha_i), uniformly over the
deviator. Thus terminal and finite-average payoffs differ by O(1/H)
uniformly over every unilateral strategy and over the prescribed law.
The table-specific constants can grow with M and throughout the thick
box: the theorem first fixes one table/profile/target and only afterward
varies the accuracy and horizon. The same-profile uniform claim is valid.

The source's two named declarations were inspected in place:
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`,
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
Their contracting-opponent hypotheses are supplied here for every player;
the saturated-opponent boundary condition is consequently irrelevant.
No Lean compilation or new Lean producer is claimed by this review.

## 5. Exact calibrations and verdict scope

I independently multiplied the displayed three-player and four-player
comparison/inverse matrices; their inverse and determinant claims check.
For the three-player equal-hazard calibration, H1=H2=0 and
H0=q(1−q)[Mq(2−q)−1]. At M=4/3,q=1/2, the shifted selected Quit value
is1/3, its stopping contribution1/4 and opponent absorption3/4. Therefore
its full payoff is4/3 and the other two full payoffs are1, as stated.
The finite-terminal constant shift is valid for EVERY response because
proper opponents force absorption independently of that response.

The bounded-data payoff limit(7) follows from Q=U and the exact selected
Q monomial. Other recipients have U_i=s_i+O(t), and the selected recipient
has the nonvanishing extra AΠ[j∈S*\{a}]z*_j. This asymptotic limit is across
different reward tables, not a varying target inside one uniform-equilibrium
claim.

No objection remains within Sections1–5. This is an actual raw-data
producer on the stated unbounded region, with a full consumer. Its new
reward-class coverage still depends on the separately checked whole-source
comparisons, not on the algebraic fact that one-column positivity is weaker
than all-entry inverse positivity.

## 6. Narrow signed-coefficient assumption removal

The author proposes replacing v=Gamma^(−1)e_a>0 and the positive selected
reward by

    sigma∈{−1,1},  v=sigma Gamma^(−1)e_a>0,
    r_a(S*)=sigma A M+c,       A>0.

I independently checked ONLY this statement delta; it passes. The exact
leading field is sigma A P(z)e_a−Gamma z. With the SAME positive
rho=(AP(v))^(−1/d), z*=rho v satisfies both AP(z*)=rho and
Gamma z*=sigma rho e_a. Its derivative is

    J=−Gamma+sigma A e_a(grad P(z*))ᵀ.

Consequently

    det J=det(−Gamma)[1−sigma A grad P(z*)·Gamma^(−1)e_a]
         =det(−Gamma)[1−A grad P(z*)·v]
         =−d det(−Gamma).

The finite polynomial cancellation, bounded and scale-thick parameter IFT,
and arbitrary-sign full-response consumer above are unchanged. This is a
large NEGATIVE participatory reward when sigma=−1, not a reversal of any
player's preference relation. The new sign is explicitly covered by this
bounded mathematical verdict. No new negative-sign fixture or its coverage
claims were checked here; the final packet can retain the already reviewed
positive-sign separating fixture without needing such a claim.

## 7. Final signed assembly: faithful-incorporation check

Final source SHA256
`8d78c71867cc6348f8e4b95abef6602b15bb57ff96f0e33961029305b0a72506`.
I checked the final signed theorem, polynomial, positive root, Jacobian,
determinant and selected-payoff formula against Sections1–6 above.
Faithful incorporation PASS: the sign is present everywhere needed, both
signs cancel in the determinant, scale-thick and full-response scopes are
unchanged, and no unreviewed negative-sign fixture entered the packet.
The existing mathematical PASS applies to those final bytes and scopes.
This was a bounded transcription/assumption-removal check, not another
proof audit or an independent audit of the complementary Section6 coverage.

## 8. Bounded standalone handoff assembly check

Checked `CODEX_ROOT__SIGNED_SINGLE_COLUMN_JACKPOT_HANDOFF.md`, SHA256
`a1767d7626a347a373c888225131ec75de7af27b3d0501baf6ed5afbfc937ff0`,
against the frozen signed source
`8d78c71867cc6348f8e4b95abef6602b15bb57ff96f0e33961029305b0a72506`
and both completed independent reviews. Verdict: faithful incorporation
and self-containment PASS. This is not a repeated proof or coverage audit.

The entire mathematical text of Sections1–5 is unchanged. The only
within-section byte delta is a duplicated Section5 heading in the handoff;
it is cosmetic and deleting one copy needs no new mathematical review.
In particular no premise concerning finite cardinality, independence,
complete responses, signed strict-column positivity, recipient membership,
compact parameter sets or the scale-thick parameter order was dropped.

Section6 faithfully retains the reviewed full-four-player raw matrix,
singleton/pair/triple/grand completion, pole/asymptotics, entire sure-owner
exclusion and every-child exact unsafe witness. Section7 is a SUBSET of
the already checked concrete comparisons: premium-trap closure, all-weight
singleton charges, full-inverse signs, every ordered partner lower face and
the zero-child-debt outsider contradiction. Their named declaration/file
correspondences and bounded, non-exhaustive novelty caveat are retained.
The handoff adds no unknown-radius exclusion or stronger architecture
completeness claim. Complementary fixture verification remains the other
finished review's mathematical scope.

Section8 accurately separates the raw producer from the existing contracting
stationary consumers and identifies the additional scale-thick substitution.
The full statement, proof, exact tests and relevant finite source boundaries
are present without any dependency on conference notes, exports or feedback.
No mathematical correction, dropped assumption or unresolved self-containment
issue was found. The ordinary-mathematics/not-Lean status is explicit.
