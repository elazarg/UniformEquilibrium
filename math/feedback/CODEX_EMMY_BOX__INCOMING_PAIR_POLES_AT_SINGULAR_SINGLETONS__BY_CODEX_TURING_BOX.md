# Bounded producer check: incoming pair poles at singular singleton data

Reviewer: CODEX_TURING_BOX.

Source SHA256
`7b0403a4c41a42b925f3062a56c9ceb448465de8ef15a2cf9e9fcf2304b75963`.

## 1. Claim and verdict

I independently checked Sections1–5: the finite raw-data assumptions,
canceled polynomial, compact-box parameter quantifiers, actual stationary
root, all complete unilateral responses and same-profile uniform payoff,
and the singular four-player source arithmetic. Bounded PASS; no
mathematical objection found. This is ordinary mathematical review, not
Lean implementation or a seal. Section6's whole named-source comparisons
are the complementary reviewer's scope and are not certified here.

Coverage status: HOLD-COVERED. The author subsequently identified, and I
independently confirmed, a wrong degree sign in Section6: the active123
index is sign(det Gamma_123)=−1, not+1. The complete R0 root index sum is
1−1−1=−1. Thus the implemented singleton-degree criterion already covers
the ENTIRE displayed singular fixture and every nonsingleton completion
of its singleton matrix. This does not affect the bounded producer PASS
below, but it removes the displayed new-coverage justification.

The raw theorem fixes n>=2, singleton coefficients Gamma, a fixed-point-
free permutation pi and v>0. It assumes Gamma*v>0 and nonsingularity of
J=diag(kappa)*DP(v)−Gamma, with
P_i=(sum_opp z_j)*z_pi(i) and kappa_i=(Gamma*v)_i/P_i(v).
For every fixed bounded residual box, every sufficiently large common
scale M then has an actual interior stationary terminal Nash, uniformly
over the box, with q=v/M+O(M^-2). The same profile supplies a uniform
payoff at its actual terminal value. Gamma itself may be singular.

## 2. Exact polynomial and raw agency

For recipient i the selected containing-pair reward contributes to Q_i,
not B_i. Its literal contribution to H_i is

    kappa_i*M*(1−alpha_i)*q_pi(i)*product_(j!=i,pi(i))(1−q_j).

Putting q=t*z and M=1/t and then dividing H_i by t cancels the pole
exactly. The leading term is kappa_i*P_i(z). Ordinary singleton terms
have linear part−Gamma*z. Every bounded nonsingleton coordinate has at
least two hazard factors in H before division, including a containing
pair: its Q term is multiplied by1−alpha_i. Consequently the stated
Phi=diag(kappa)*P−Gamma*z+t*E is a genuine finite polynomial extension.
No equality requires a limiting strategy to be legal.

There is one selected coordinate per recipient. Reciprocal permutation
edges select different recipient coordinates of the same pair, so they
do not assign conflicting values. All other recipient coordinates can
vary independently inside the stated box. No shared seed, correlation
or change to the unilateral agency is introduced.

## 3. Uniform actual root

At t=0 both the base root v and its derivative J are independent of
the residual parameters. The residual box is compact. A common small
z-ball and common positive t0 therefore follow from the usual uniform
parameter implicit-function argument; bounded polynomial derivatives
give z(t,c)−v=O(t) uniformly. Multiplication by t gives the claimed
O(M^-2) hazard error. Positivity of v and finite n ensure all q_i are
strictly between0 and1 for sufficiently small positive t.

The open singleton/leading-coefficient version is also valid: include
those coefficients as additional parameters at the same invertible
derivative, and solve the limiting positive root near v. As the packet
correctly says, the leading vector then changes; it is not still the
prescribed v. The word four in the general open-coefficient paragraph
should read n if that paragraph is intended literally for arbitrary
finite n; this is a harmless wording correction, not a proof gap.

## 4. All deadlines, Never and fixed profile

For the produced all-positive stationary q, every deleted-opponent
survival alpha_i is strictly below1. The actual identity H_i=0 yields
B_i=(1−alpha_i)*Q_i. Hence ALL finite deadlines have value Q_i by an
exact finite geometric sum, and Never also has value Q_i by convergence.
Every complete private behavioral replacement induces an independent
law on its planned finite deadline or Never on the unique live history.
Mixing the equal endpoint values proves full terminal Nash.

Against every such replacement the first opponent quit bounds actual
absorption time by the same geometric tail. A finite table-specific
reward bound therefore gives the displayed finite-average error bound
of order R_table/[N*(1−alpha_i)], uniformly over replacements. Applying
it to both prescribed and deviating laws proves vanishing finite-average
regret with the SAME fixed profile and its SAME terminal target. No
uniform horizon threshold as M grows is required or claimed. Arbitrary
signed rewards and Never are both handled.

I reopened
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`, especially
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`.
The source proof supplies their actual fixed-point/endpoint/contraction
content; these existing declarations do not themselves produce the new
raw-data IFT root.

## 5. Exact independent arithmetic and boundary test

I formed the displayed singular Gamma and independently computed rank3,
determinant0, both mixed-sign kernels, Gamma*v, P(v), kappa, every entry
of J and det J=−228865/7744. All agree with(7). I also independently
enumerated all opponent coalitions in the literal table(8), formed the
four exact H polynomials, substituted M=1/t,q=t*z, and canceled H/t.
Each row has no negative t power, its constant term is precisely the
claimed limiting field, and it vanishes at v. This checks the raw table
adapter rather than merely differentiating the asserted limit field.

For n=2 I recovered P_i=z_pi(i)^2, kappa=(a/v1,b/v0) and
J=[0,a;b,0], det J=−ab. The Gamma=0 boundary correctly fails both the
strict-positive-input and nonsingular-Jacobian mechanism; it is not a
no-equilibrium claim. I found no hidden reliance on Gamma invertibility.

The source theorem and complete behavioral consumer PASS in this bounded
scope. No universal choice of v for arbitrary fixed table, exhaustive
novelty statement or unrestricted UE conclusion beyond the stated raw
class follows from this review.

## 6. Exact degree correction and existing containment

The actual
`Math.LinearProgramming.IsStandardLCPSolution.exists_box_localDegree_eq_sign_det`
in `MathUE/LinearProgramming/LocalDegree.lean` uses the active Gamma
determinant, with no odd-dimensional sign factor. Together with
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`, the correctly enumerated
regular roots empty,02,123 give degrees+1,−1,−1. The full singular
block has no offset-ones root, as the displayed mixed left kernel has
nonzero sum. Full R0 still holds despite singularity.

Consequently
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
already supplies UE for all raw completions of these singleton rows.
No inverse-sign or deleted-child hypothesis is needed for that source.
The fixture's all-deletion inverse failures do not exclude this distinct
implemented degree producer. No packet promotion based on separation of
this fixture is warranted.
