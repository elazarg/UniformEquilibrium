# Two opposite participatory poles: bounded producer review

Reviewer: CODEX_TURING_BOX.

Reviewed source: `CODEX_EMMY_BOX__TWO_OPPOSITE_POLES_PROJECTIVE_SELECTION.md`,
SHA256 `2ecba7c69a9f73503dfefd451b3a01701b06665a80e081bbbbee77f7b65792ce`.

## 1. Claim and scope

I independently checked Sections1–5: the exact scaled polynomial, the
uniform transverse/radial implicit solver, its continuous scalar residual,
the interval selection, scale-thick residuals including degree1, and the
complete-deviation/same-profile uniform-payoff consumer. Verdict: bounded
adversarial PASS; no mathematical objection remains in that scope.

The claim is a raw-data producer for arbitrary finite n>=2, not a supplied
stationary-root verifier. The inverse need not have a same-signed column:
one positive direction u−x*w on a compact bracket and opposite endpoint
signs of the displayed scalar G suffice. The two selected coalitions have
the SAME size d+1 and each contains its own reward recipient. Both
restrictions are used. Distinct recipients are used in the coordinate
split; the selected coalitions themselves may coincide.

I did not audit all Section6 whole-source/novelty comparisons. Its exact
Gamma, inverse-direction endpoints and scalar formula were checked as a
positive calibration of the new producer, not a coverage verdict. The
complementary fixture/coverage review remains separate.

## 2. Exact field and pole degrees

For recipient i the stationary endpoint quantities are literal Q_i,
B_i, alpha_i, with H_i=(1−alpha_i)Q_i−B_i. A selected containing coalition
S_i appears only in this recipient's Q_i. Changing its reward coordinate
cannot affect any other recipient's H coordinate. The two pole terms
therefore add independently, even when S_a=S_b.

With |S_i|=d+1, q=t*z and M=t^(−d), division of that term by t leaves

    [(1−prod_opp(1−t*z_j))/t]
       *sign_i*C_i*prod_(S_i\{i})z_j*prod_(I\S_i)(1−t*z_j).

This is an exact polynomial with leading term sign_i*C_i*P_i(z).
An ordinary participatory nonsingleton coordinate has degree at least2
because the Q monomial is also multiplied by 1−alpha_i. An ordinary
nonparticipatory nonsingleton coordinate enters B_i with degree at least2.
The singleton degree1 field is exactly −Gamma*z. Consequently (5) is an
exact polynomial identity, not just a pointwise asymptotic expansion.

I symbolically checked the selected-coalition monomial for every recipient
and every containing coalition at n=2,3,4,5. All had nonnegative t powers
and the stated leading P_i. This finite test supports the general degree
argument above; it is not its substitute or a Lean proof.

## 3. Uniform partial solver and scalar continuity

In (6), Gamma*z has coordinates h, −h*x, y_C at a,b,C respectively.
At t=0, Phi_C=−y_C exactly, including its derivatives in h and x.
The positive a root h0 satisfies A*h0^d*P_a(v)=1. Thus the derivative of
Phi_a in h is d, and the (h,y) Jacobian is block upper triangular with
diagonal d and −Id_C. Its inverse is uniformly bounded on the compact
positive branch. The case n=2 has an empty C block and the nonzero scalar
derivative d; there is no missing transverse equation.

I actively checked the possible chart-gluing issue. A common tubular
neighborhood exists because h0, v and the matrix inverse vary continuously
over a compact parameter set, with strictly positive h0 and v. Uniform
continuity of the derivatives gives a common contraction radius and a
common small t bound. Local solutions sufficiently near h0(x),0 then
agree on overlaps by local uniqueness in that tube. This produces the
continuous partial solution on the WHOLE bracket. No uniqueness or
continuous selection of the final angular zero x(t,c) is needed.

Division by h in g_t is safe uniformly. At t=0,

    Phi_b/h = x−B*h0^d*P_b(v)
            = x−(B/A)*P_b(v)/P_a(v).

Both the partial solution and this residual converge uniformly over x and
the bounded residual box. The strict endpoint signs consequently persist
for one common small t threshold. IVT supplies some interior zero for
each individual residual table. The resulting z stays in a common bounded
positive set, so further shrinking t gives every q_i strictly between0
and1. This is enough for the stated producer quantifiers; no continuous
table-to-final-root selection is asserted or required.

The same compactness argument applies when singleton/coefficient/bracket
data vary on a compact subset of the strict domain. One must keep the
coalition labels and d fixed, as the statement does. Positivity and the
endpoint margins then have common positive lower bounds.

## 4. Scale-thick region and d=1

Substitution of each ordinary residual by e/t lowers its least t power
from1 to0 in H/t. The selected residuals have least power d before this
substitution and hence d−1 afterwards. All powers remain nonnegative.
At (t,e)=(0,0) the same branch and invertible (h,y) Jacobian remain.

Applying the common solver to (t,e), not pretending that e disappears
at t=0, gives a small parameter rectangle on which the endpoint signs
persist. Choosing one kappa inside that rectangle proves simultaneous
bounds |c_i|,|other nonsingletons|<=kappa/t for all sufficiently small t.
This includes d=1: some e terms survive at t=0, but are small parameters
around e=0. No asymptotic assertion uniform over the scale-thick box is
needed or stated. This removes the main plausible degree-one falsifier.

## 5. Full agency, Never and finite horizons

H_i=0 and alpha_i<1 give B_i=(1−alpha_i)Q_i. Every finite deadline then
has payoff Q_i, and the geometric sum for Never gives the SAME Q_i.
Private behavioral replacement on the unique live history is a law over
these complete deadlines and Never, so integrating cannot change the
payoff. This verifies unrestricted terminal Nash, not merely one-row or
stationary best replies. No nonnegative reward or own-singleton premise
was used.

Every player has a proper opponent because n>=2 and all produced hazards
are positive. Under ANY replacement law, that opponent process bounds
absorption by a geometric tail alpha_i^t. The expected time-to-absorption
bound therefore controls terminal versus finite-average payoff uniformly
over all replacements. A finite table-specific reward bound suffices even
though the selected rewards grow with M. The same fixed produced profile
converges to its actual terminal vector and has vanishing finite-horizon
regret. Thus the packet's same-profile UE conclusion has the required
fixed-target and all-long-horizon quantifiers.

The semantic pattern agrees with
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`, inspected
for the preceding one-column consumer. Those declarations do not themselves
produce the new partial-IFT/IVT root; that part is ordinary mathematics here.

## 6. Exact small tests

For the two-player Gamma=[0,a;−b,0], a,b>0, I independently obtained
v=(x/b,1/a), P_0(v)=1/a², P_1(v)=x²/b². Therefore
G=x−(B/A)*a²*x²/b² has its positive sign-changing root. Substitution of

    q1=a/(A*M+c0−s0),    q0=b/(B*M−c1+s1)

into the actual H equations gives zero exactly. The denominators are
positive and exceed the numerators for all sufficiently large M, for
arbitrary fixed signed singleton/residual values.

For the displayed Fin4 matrix I independently recovered det Gamma=63,
the v endpoint vectors, and

    G=(36*x³−183*x²+454*x−121)/[(3*x+1)*(12*x+25)],
    G(3/10)=−149/27170,
    G(31/100)=100818/1732175.

Both endpoint vectors are strictly positive. This is an actual nonempty
raw domain with strict margins, not merely a formal conditional theorem.
The broader Section6 separation assertions were outside this bounded check.

## 7. Narrow recipient-membership and mixed-size deltas

The author separately proposed these assumption removals, without changing
the frozen source above. I checked precisely the following algebraic deltas;
both PASS. This is not a re-audit of fixture coverage or final incorporation.

For a selected coalition S_i NOT containing its reward recipient i, set
d_i=|S_i|−1>=1 and give that coordinate raw reward K_i*L^(d_i)+c_i.
It contributes only to B_i and hence contributes

    −K_i*product_(j in S_i)z_j

to H_i(t*z)/t at t=1/L=0. Thus the positive homogeneous polynomial is
P_i=product_(S_i)z_j, of degree d_i+1. The containing-recipient case uses
P_i=(sum_opp z_j)*product_(S_i\{i})z_j, of the SAME degree. Choose the raw
sign according to membership to obtain the desired +A*P_a and −B*P_b
field terms. This is a recipient-specific reward change, not utility
reversal. Each selected coordinate still affects only its recipient.

If the two sizes differ, scale their raw rewards by L^(d_a) and L^(d_b)
respectively. Each pole separately has an exact polynomial extension at
t=1/L=0. The partial solver has

    h0(x)=[A*P_a(v(x))]^(−1/d_a),
    radial derivative d_a,
    G(x)=x−B*[A*P_a(v(x))]^(−d_b/d_a)*P_b(v(x)).

The transverse block remains −Id. Every displayed P stays strictly
positive on the compact positive-direction bracket. The same common
implicit solver and strict-sign IVT therefore apply. The scalar G need
not be rational in the mixed-degree case; its continuity and strict
endpoint signs, not rationality, are what the proof uses.

An ordinary nonsingleton residual e/t still has nonnegative t powers.
For a selected residual the least power is d_i−1, whether its recipient
belongs to its coalition or not. Thus d_i=1 and the simultaneous scale-
thick residual bound kappa*L are covered exactly as in Section4 above.
No degree-zero/singleton selected pole is admitted by this delta.

I independently recovered the author's new same-Gamma calibration with
a=0,b=1,S_a=S_b={1,2,3}: raw r_0=−14M is passive and raw r_1=−M is
participatory. Both d_i=2; the leading field has signs +14*P_0 and −P_1.
Its scalar is exactly

    G=(42*x²+23*x−11)/[14*(3*x+1)],
    G(3/10)=−8/665,
    G(31/100)=831/135100.

This checks the new raw-to-field sign correspondence and a nonempty
strict bracket. Its additional whole-source separation claims, if any,
are outside this narrow verdict.

## 8. Final mixed-size/membership incorporation

Final source SHA256
`8b9346560401c8f6032424b0f1640caf5551f2ecaf2674d9b82fb340eae0e5e7`.
I checked faithful incorporation of the bounded producer and Section7
deltas above. PASS: epsilon membership signs in the raw statement give
the claimed opposite FIELD signs, t=1/L cancels each separate degree,
P_i has degree d_i+1 in both membership cases, the h0/radial derivative
and b residual use the correct d_a,d_b exponents, and the scale-thick
and full-response quantifiers are unchanged. The original grand fixture
uses L=M^(1/3), and the checked passive/participatory triple calibration
uses L=M^(1/2), as required. The handoff retains the actual raw-data
root-production obligation rather than assuming that root exists.

The producer PASS applies to these final mathematical scopes and bytes.
This was a bounded faithful-incorporation check, not another full audit.
Section6's whole-source comparisons, including the new Section6.5
coverage assertions, remain the complementary reviewer's scope; the
exact Section6.5 field/scalar calibration was checked in Section7 above.

## 9. Replacement determinant49 fixture: bounded exact check

Source SHA256
`1fdacd2d8e8566bf09f0cbdb85970a6faea99722df81d0ee7b0e94d8fd73e324`.
HOLD-COVERED for the claimed separating fixture. The matrix, bracket,
complementarity roots and all-deleted inverses below are correct, but my
initial check accepted the WRONG sign convention for the odd-cardinality
active root. The corrected canonical degree is−1, not1, so the entire
fixture is already covered by the implemented singleton-degree criterion.
Sections1–5 retain the
previously checked producer, including mixed sizes and arbitrary recipient
membership. Their producer PASS does not imply new raw-table coverage.

I independently reconstructed det Gamma=49 and the complete displayed
inverse. Every inverse column has both strict signs. For recipients1,2,
the direction is exactly

    v=(5−8x,31x−1,19−x,6+10x)/49.

It is positive throughout [3/10,8/25]. Direct substitution into the
participatory grand polynomials gives precisely the rational scalar and
both strict endpoint signs in(11). For the two negative raw023 rewards,
the passive recipient1 and participatory recipient2 give respectively
P_a=z0*z2*z3 and P_b=(z0+z1+z3)*z0*z3. These give exactly(16), with the
claimed reversed endpoint signs. The orders L=M^(1/3) and L=M^(1/2)
match the respective selected coalition sizes.

All eleven principal blocks of size at least2 are nonsingular. Enumerating
their unique offset-ones active-system candidates yields only supports02
and123 as nonempty complementarity solutions, with the displayed vectors,
strict inactive residuals and indices−1,−1. Together with the empty root,
the regular index sum is−1. Singleton active systems are impossible because
their diagonal is0 and their offset is1. For the homogeneous problem, an
active block of size at least2 would annihilate a nonzero active vector;
invertibility excludes it. A singleton homogeneous support fails at its
strict negative external column entry. Thus the stated R0 calculation is
valid. Every row also has a strict negative off-diagonal blocker.

I independently computed all four natural-order deleted inverses and
obtained exactly the four matrices displayed in Section6.1. Each has a
negative entry. I reopened
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`:
`childMatrix` is the literal principal singleton-difference matrix, and
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
requires its inverse to be entrywise nonnegative. Therefore every possible
three-player child fails this prerequisite, before any outside-row weight
test. This is a whole child-selection exclusion for that named declaration,
not an assertion that all other selective lifts or unknown sources fail.

The actual declaration
`Math.LinearProgramming.IsStandardLCPSolution.exists_box_localDegree_eq_sign_det`
in `MathUE/LinearProgramming/LocalDegree.lean` gives sign(det Gamma_CC),
with NO factor(−1)^|C|. The global sum is the canonical `r0Degree`, by
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`. The regular123 determinant
is−2, so its index is−1. The already inspected
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
therefore covers EVERY nonsingleton completion with this singleton matrix.
The same correction applies to the singular incoming-pair fixture, whose
proper active roots have the same determinants and indices. An R0 matrix
may be singular, so singularity does not evade that theorem.

The author identified this error; I independently confirmed it against the
actual declarations. My earlier accepted index convention is withdrawn.
Both producers remain mathematically valid, but neither displayed fixture
can establish new class coverage. The determinant63 fixture's separate
passive-row containment also remains valid.
