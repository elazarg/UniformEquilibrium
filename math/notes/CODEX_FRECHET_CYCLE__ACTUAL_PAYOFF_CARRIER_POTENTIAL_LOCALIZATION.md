# Actual payoff-carrier localization of a root potential

Identity: CODEX_FRECHET_CYCLE.

Status: bounded localization test finished and paused; ordinary mathematical
proof below, not Lean-checked. The bounded
payoff realization is a genuine additional actual-source statement. The
potential localization yields complete scalarized incentive inequalities and
a binding-face restriction, but does not yet exclude a universal potential
or establish an equilibrium of the original game. Section 8 records the
final global support-minimum/repetition comparisons and their exact failure
to supply the needed incentive comparison. Caps are not preserved by
the payoff realization. No export is proposed at this checkpoint.

## 1. Question and semantics

Let I be a finite nonempty player set, n = |I|. Every nonempty quitting
coalition S has a reward vector r(S) in R^I, with |r_i(S)| <= M and M > 0.
The preabsorption and Never payoffs are zero. Strategies and deviations are
unrestricted behavioral strategies with independent private randomization.
Reading the unique live history identifies them, for all terminal payoff
purposes, with independent laws on N union {Never}. No public mixture is used.

Write U(sigma) for the complete terminal payoff vector. Let

    K = closure { U(sigma) : sigma is an actual product profile }.

For a product root q in [0,1]^I and continuation v, set

    c(q) = product_i (1-q_i),       a(q) = 1-c(q),
    F(q,v) = c(q)v + sum_(S nonempty) Pr_q(S) r(S).

Let Q_i(q) and C_i(q,v) be the literal Quit and Continue endpoints, and let

    R_i(q,v) = max(Q_i(q), C_i(q,v)) - F_i(q,v)

be ordinary root regret. Exact Nash means R_i = 0 for every i. Set
s_i = r_i({i}) and p^i = r({i}); s is not a terminal reward vector in general.

Suppose a C1 function H on a neighborhood of a box containing [-M,M]^I
satisfies the universal robust charged-root inequality for some delta > 0:

    H(w) + a(q) <= H(v)

whenever v,w lie in that box, |w-F(q,v)|_infinity <= delta a(q), and every
R_i(q,v) <= delta a(q). A rational polynomial certificate from the current
fixed-box characterization is a special case. The main application is normal
Fin4 data with a positive singleton, but no normality is needed for the
payoff realization or the conditional localization proved here.

The test is to minimize H on K and use an actual source for that minimum,
rather than an ambient box anchor. Neither convexity of K nor attainment by
a behavioral profile is assumed: the latter is proved for PAYOFFS below.

## 2. Bounded finite-menu realization of the whole payoff carrier

### Theorem 2.1

Every v in K is exactly U(sigma) for some product profile whose stopping laws
are supported on {0,...,N-1,Never}, where N = n(n+1). Thus K is already the
actual payoff image, is compact, and equals the image of this single finite
product simplex. For Fin4 one may take N = 20.

This statement preserves only the n prescribed payoff coordinates. It makes
no assertion about response caps, debt, equilibrium, or the original dates.

### Proof

First take an arbitrary actual profile. Censor each player's finite atoms
after a large cutoff to Never. The total variation errors tend to zero:
they are precisely the finite tail masses, not the mass at Never. Product
coupling changes each bounded payoff by at most 2M times the sum of the
marginal errors. Thus arbitrary actual payoffs are approximated by payoffs
of independent finite stopping laws.

Now fix any one such finite-law profile. Holding the other players fixed,
the full payoff vector is a convex combination, with player i's own mixing
weights, of vectors

    V_i(t) = U(sigma[i <- QuitAt t]),

including t = Never. These are vectors in R^n, not only player i's payoff.
Finite affine Caratheodory gives a combination of at most n+1 of the same
actions with exactly the same vector. For completeness, if more than n+1
positive weights remain, their augmented vectors (V_i(t),1) are linearly
dependent. Move the weights along a nonzero dependence, preserving both the
sum and the vector, until one weight first becomes zero. Iteration proves
the asserted support bound without introducing any new pure action.

Perform this replacement successively for all n players. At each step the
CURRENT whole payoff vector is preserved; already compressed players retain
their support bounds. The final independent tuple therefore has the same
payoff vector and at most n(n+1) distinct finite dates in its combined
support. The count includes no more than this number even if some of the
retained actions are Never or dates are shared.

List those occupied finite dates in increasing order and map them to
0,1,...,L-1, where L <= N. Fix Never. Under every pure support tuple, the
earliest quitting set and all ties are unchanged. Hence the prescribed
terminal coalition, and therefore the whole prescribed payoff vector, are
unchanged. The result is an actual profile in the one menu F_N.

The payoff map on the finite product of F_N simplexes is a finite
multilinear polynomial in the private action probabilities, and hence has
compact image. We have just shown that every arbitrary actual payoff is
in the closure of this image. Compactness puts it in the image itself;
the same argument applies to every v in K. The reverse inclusion is literal
behavioral realization of finite independent laws. QED.

The argument deliberately takes a compact limit only AFTER reaching one
uniformly bounded menu. It does not take an uncontrolled weak limit of
terminal payoffs under the original stopping laws.

## 3. Prefix invariance and an attained H minimum

K is nonempty and compact. It contains 0 and every r(S), realized by
all-Never and by a pure date-zero coalition. If v is in K and q is any
product root, then F(q,v) is in K: prefix q to an actual representative of
v. Alternatively, prefix a realizing sequence and use continuity of F.

Choose x minimizing H on K and let h_* = H(x). Theorem 2.1 supplies one
actual F_N profile sigma with U(sigma) = x. All incentive statements below
are derived AFRESH from minimization over the FULL actual payoff carrier,
after this representative has been chosen. No deviation comparison is
transported through the date compression in Theorem 2.1.

For every q, H(F(q,x)) >= h_*. Consequently, if a(q) > 0, then

    max_i R_i(q,x) > delta a(q).                         (3.1)

Otherwise the exact Bellman endpoints would be a robust edge, contradicting
minimality. Finite-game Nash existence supplies an exact root at x. By
(3.1) it must have a = 0 and hence q = 0. At q = 0 the endpoint comparisons
are s_i versus x_i, so

    x_i >= s_i for every i,
    and every exact root at x is all Continue.          (3.2)

This is now an ACTUALLY realized root-inert payoff, not a fictitious anchor.
It is not an original-game Nash conclusion about sigma.

## 4. The actual whole-strategy inequalities

Put g = gradient H(x). For any player i and any complete unilateral law tau,
let y = U(sigma[i <- tau]). Mixing only this player's stopping law with
weight theta in [0,1] gives the actual payoff

    x(theta) = (1-theta)x + theta y.

Thus H(x(theta)) >= H(x), and differentiation at theta = 0 gives

    g dot (y-x) >= 0.                                  (4.1)

The inequality holds simultaneously for all unrestricted behavioral tau.
In other words, sigma is an exact terminal Nash profile in the common-COST
game with scalar terminal cost g dot r(S), which every player minimizes.
It is generally not Nash for the original vector rewards. If g = 0 this
scalarization is vacuous; the proof does not assume g is nonzero or has a
favorable coordinate sign.

Pure-time expectations give the exact equivalent test

    g dot (V_i(t)-x) >= 0 for every i and every t or Never.

Because all opponents of sigma use dates below N or Never, every finite
t >= N has the same payoff vector as t = N. The unrestricted test therefore
has the finite representatives {0,...,N,Never}; the late date N must NOT
be dropped merely because it is outside the played menu F_N.

Moreover, if an action t has positive mass in sigma_i, then

    g dot (V_i(t)-x) = 0.                              (4.2)

Indeed the nonnegative quantities in (4.1), averaged with the player's
own finite weights, sum to zero. Equivalently, this supported mixture can
be varied a small amount in either sign, so ordinary first-order minimum
optimality gives equality.

Independent pure solo prefixes supply a second family of genuine feasible
segments: (1-theta)x + theta p^i lies in K. Therefore

    g dot (p^i-x) >= 0 for every i.                    (4.3)

This does not give g dot (r(S)-x) >= 0 for every coalition. The whole
carrier is not assumed convex; a mixture of arbitrary terminal coalition
vectors is not silently declared independently realizable.

## 5. Carrier growth below a singleton and binding-face rigidity

For every v in K and every i,

    H(v) - h_* >= (s_i-v_i)_+ / (4M).                 (5.1)

To prove this, let h = s_i-v_i > 0 and choose an exact root q at v. Put
rho = 1-product_(j != i)(1-q_j). The event of opponent absorption changes
the Quit endpoint from s_i by at most 2M rho and the Continue endpoint
from v_i by at most 2M rho. Hence

    Q_i(q)-C_i(q,v) >= h-4M rho.

If q_i < 1, the Nash condition for the supported Continue action gives
Q_i <= C_i and hence a(q) >= rho >= h/(4M). If q_i = 1, then a(q)=1
and the same bound holds since h <= 2M. Prefix invariance puts F(q,v)
in K, and exact-root drift gives

    H(v)-h_* >= H(v)-H(F(q,v)) >= a(q) >= h/(4M).

The case h <= 0 is ordinary minimality. This proves (5.1).

Let J = {j : x_j = s_j}. For any one-sided differentiable actual-payoff
path v(t) in K with v(0)=x and derivative d, (5.1) implies

    g dot d >= (-d_j)_+/(4M),       j in J.             (5.2)

In particular, every two-sided differentiable feasible path has
g dot d = 0 and d_j = 0 for all j in J. Applied to a supported action of
the finite representative, this yields the exact extra constraint

    V_i(t)_j = x_j = s_j
    for every player i, supported action t of sigma_i,
    and binding coordinate j in J.                   (5.3)

Thus the source does add more than ambient all-Continue optimality:
every supported one-player payoff variation is tangent to ALL binding
singleton faces. Neither (5.3) nor (4.2) constrains an unsupported response
to be unprofitable for its original owner.

## 6. Where the scalar/vector bridge presently stops

The actual finite representative supplies the original response vectors
V_i(t)-x, not arbitrary directions. Nevertheless (4.1) constrains their
scalar projection onto ONE common g. Original equilibrium would require
their respective OWN coordinates to be nonpositive:

    V_i(t)_i-x_i <= 0 for all i,t.

Those are different statements. A profitable own coordinate can be offset
in (4.1) by the other players' payoff changes. No sign condition on g or
joint realization of separately favorable counterfactual vectors has been
derived. Even the binding-face condition permits unsupported profitable
actions; in the strict region x_i > s_i for all i it supplies no binding
coordinate at all.

There is a second exact state-matching issue. The root q_t prescribed by
the finite representative sees its literal tail payoff u_(t+1), not the
total payoff x. Scalarized optimality of an actual root against that tail
does not make q_t an original vector Nash root, either against u_(t+1)
or against x. Root Nash existence at x produces only all Continue by (3.2).
Replacing a prescribed row by a vector-Nash root at its literal tail gives
a decrease from H(u_(t+1)), which need not be the minimum h_*. No comparison
making that decrease fall below h_* has been obtained.

These are the remaining implications to test. They are not claims that a
global certificate exists, or that actual-source localization cannot work.
The finite realization and inequalities above remain valid independently
of whether that bridge can be closed. No finite Nash, cap preservation,
uniform-equilibrium existence, positive-gap example, or new polynomial
certificate class follows from the present proof.

## 7. Named sources and bounded overlap check

The current toolkit route led to the following declarations, read in their
defining files:

- `quittingTerminalSemanticCarrier_isCompact`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`, and
  `quittingTerminalSemanticPrefix_mem_carrier`, in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
  Their payoff projection gives the compact invariant K used here.
- `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`, in
  `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`:
  the finite product-simplex image is the actual behavioral payoff image.
- The stopping-law payoff expectation and full pure-time extremality
  interfaces in `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`
  and `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
  They concern independent laws and unrestricted deviations, including Never.
- `quittingRootEndpointDifference_ge_singletonGap_sub_four_mul_of_tail_bound`,
  consumed in `UniformEquilibrium/Quitting/Root/SingletonGapSemanticDebtDescent.lean`.
  Equation (5.1) uses the same elementary endpoint estimate, with H-minimality
  in place of a semantic-debt comparison; it is not advertised as a new
  endpoint bound.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`,
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`,
  supplies the current conditional Fin4 motivation. It is not an
  unconditional certificate producer or a theorem of nonexistence.

The whole earlier all-anchor and projected-anchor notes do not use actual
payoff attainment; their minimizing anchor need not be realizable. The
bounded lookup found no existing uniform F_(n(n+1)) PAYOFF-only realization
in the toolkit or the named timing/semantic sources. This is not a worldwide
priority claim. Caratheodory itself is classical elementary mathematics.

The nearby `CODEX_SPINOZA__FOUR_DEADLINE_SEMANTIC_COMPRESSION_AND_SINGLE_HOST_BUBBLE.md`
was checked through its deterministic compression: it starts from two sure
clocks, installs full responses, and compresses four deterministic deadlines
while retaining the initial zero/nonzero boundary bit for caps. It does not
cover arbitrary mixed payoff carriers. The present support reduction is
payoff-only and intentionally does not inherit that note's semantic claims.

No original or frozen proof was edited, and no Lean implementation or fresh
Lean build was performed. The current open test is the scalar/vector bridge
in Section 6, not attainment of x or a new supplied-compatibility interface.

## 8. Final global comparison and stopping point

### 8.1 Minimal support does not purify an H minimum

Among all finite independent profiles realizing ANY H-minimizing payoff,
choose one with the least total number of positive-probability stopping
actions, counting Never when it has positive mass. Such a minimum exists:
Section 2 supplies a nonempty finite family, and applying its elementary
support reduction once more bounds the total support by n(n+1). The count
is a positive integer. Common date compression preserves the count and
payoff, so this representative can still be taken in F_N. In this section,
x and sigma denote this chosen payoff and representative; all earlier
minimum-source conclusions apply to them.

Suppose player i mixes at least two actions. Replacing its entire law by
ANY pure time t or Never gives an actual finite profile with strictly fewer
total support atoms. Hence, for its full payoff vector y,

    H(y) > h_* .                                      (8.1)

Equality would contradict the minimal support count; a lower value would
contradict global H-minimality on K. The comparison includes a complete
original-game best response, since at the finite representative such a
response is attained in {0,...,N,Never}. Even if it raises player i's own
payoff, it cannot lower H. For a supported action its first-order scalar
change is zero by (4.2), while the full replacement has strictly positive
H excess by (8.1). No Jensen inequality of the reverse sign is available
for the arbitrary nonconvex H.

If q is now any original exact root against y, its successor is an actual
payoff and the global potential inequality gives only

    a(q) <= H(y) - h_* .                              (8.2)

To reach a contradiction by this full-response-then-prefix construction
one would need the STRICT REVERSE comparison for some such response/root.
Minimal support provides neither a positive absorption bound at the raised
payoff y nor an upper bound on H(y)-h_* below that absorption. In particular,
raising the responder's own payoff does not create a singleton deficit.
This is the exact global comparison missing from this concrete operation,
not an assumption that the response remains in the minimum fibre.

If the minimum-support profile is already pure, there is no support-count
decrease. Replacing a pure clock by another pure clock can improve its
owner's reward without decreasing H of the resulting payoff. The scalar
and original vector incentive comparisons remain different.

### 8.2 A literal finite repetition supplies return, but not root incentives

Read the representative as its N-row actual hazard word W followed by
all Continue. Let c be its joint probability of surviving the whole word.
Its finite-block terminal reward contribution is exactly x, so putting
any actual payoff v behind the same word yields x+c v.

In the canonical application, x_0 >= 1 by (3.2), hence x is nonzero and
c < 1. Repeat the SAME root word periodically, using independent private
randomization at each live stage. This is an actual behavioral profile,
not a correlated mixture of profiles. Its eventual absorption probability
is one, and its first payoff is

    y = x/(1-c).

All phase continuation payoffs are actual, lie in K, and satisfy exact
periodic Bellman recursion. If c = 0, then y = x: the construction even
gives a literal payoff return at the attained H minimum. If c > 0, no
claim is made that H(y) is minimal.

However, summing the universal drift around this exact Bellman period
would give 0 >= sum_t a(q_t) > 0 if EVERY row had ordinary root regret
at most delta a(q_t). Therefore a supplied universal H itself forces at
least one literal row of this period to violate that bound. Global
minimality and smallest support do not supply the opposite row-incentive
estimate. The construction solves return only, not an admissible charged
return; the distinction persists even in the c = 0 case.

### Final checkpoint

The bounded consumer attempt stops here. The genuinely retained additional
fact is bounded actual PAYOFF-carrier realization, together with the exact
actual-source implications in Sections 3--5. Neither full replacement nor
whole-word repetition closes the scalar/vector incentive gap. No universal
potential has been excluded, and the finiteness statement is not a finite
equilibrium or cap-preserving strategy-class theorem.

One concrete restart question, not a supplied hypothesis or an established
claim, is whether a minimum-support H-minimizing representative can produce
an actual full replacement y and an original exact root q at y for which
a(q) > H(y)-h_*. That would directly contradict (8.2). No such comparison
has been obtained. Per the requested graceful pause, no further line or
experiment is started.
