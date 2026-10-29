# Independent full-proof review of exact opposed-pair path UE

Reviewer: FACE_REVIEW. Ordinary mathematics, not Lean checked.
Verdict: PASS, with no unresolved mathematical objection to the full
reward-table-to-uniform-payoff proof. The complete prior-producer coverage
census is assigned to a separate reviewer; this review independently checks
the new theorem, its semantic consumer, source correspondence, and exact
membership/boundary controls. It is not merely a review of the local path.

Reviewed packet: `math/exports/EXACT_OPPOSED_PAIR_PATH_UNIFORM_EQUILIBRIUM.md`,
SHA256 `d7f3fdd20419800f8e5150c5e512129a24e97ebdc365645acd68fa8f493967bf`,
628 lines. I read all eight sections. The review includes a fresh attempt to
falsify the reproduced closed-domain induction and its virtual-to-actual
passage. The path proof also has an independently constructed symbolic
checker, `/tmp/FACE_EXACT_REVIEW_CHECK.py`, SHA256
`8a35bf179add9c1cdbb3e3087f8005d27fb617a1c1b4a61e56cfcfdb53bb5716`.
The author's checker `/tmp/GENERAL_FACE_GEOMETRY_CHECK.py`, SHA256
`0e61b2dc02380eb72ef8e252b30dd54cef67355bbf83a7fae1560cf4d4f67fac`,
also passes when rerun independently.

## 1. Exact scope and supplied inputs

The packet quantifies every finite four-player reward table meeting explicit
raw inequalities, including nonnegative original own levels. The numerical
core is not a hypothesis. Both versions of the finite quadratic test are
fully raw: the bounded version uses H=-L1/s and X=W/c21, while the unbounded
version removes dependence on L1. Cases W=0 and H=0 correctly omit the tests
for impossible bad supports. The conclusion is native absorbing total debt
infimum zero, then one fixed original uniform-equilibrium payoff.

No continuation, root, strategy, punishment, actual minimum, or return
certificate is supplied as an extra assumption. The root path and degree
argument produce the selected return at every relevant continuation. The
minimum used later is selected internally from a nonempty compact closure.
Independent private randomization and complete unilateral replacement are
retained throughout. The theorem is not a characterization of all UE games
and does not close Fin4.

## 2. Path identity, finite tests, and endpoint

I rederived the two active gaps directly by conditioning on owner0. With
A=sx+d0 alpha and B=cy+e0 alpha, both numerators are positive at actual pair
odds x,y>0. C=s-d1 alpha and D=c-e1 alpha remain nonnegative up to the
chosen first-sure endpoint. Consequently both probability denominators are
positive even at that endpoint, including d0=0 or e0=0 cases.

Conditional on owner0 continuing, the quiet3 comparison is precisely
l q1(1-q2)+m q2(1-q1)+n q1q2-v3(1-q1)(1-q2).
Conditional on owner0 quitting, it is the product average of the four actual
delta entries. Clearing the positive denominator gives N_v exactly. Initial
quietness is v3>=ly+mx+nxy. Since CD>=0, replacing v3 by this binding value
increases the gap. The resulting polynomial is alpha times the displayed
R; all three coefficients were independently expanded and checked.

R is multiaffine in x,y and quadratic in alpha; its x slope is only affine
in alpha. The four-corner interpolation and constant/slope criterion on
x>=0 are therefore exact. The finite quadratic maximum test handles the
concave interior vertex with the correct inequality direction
4da-b^2>=0 when d<0. Linear, constant and endpoint cases are included.
Degenerate corner denominators are harmless: the tests concern a polynomial,
whereas the root construction uses strictly positive initial odds.

These tests are necessary and sufficient only for the binding-continuation
upper envelope. The packet explicitly avoids claiming necessity for actual
continuations or for UE. Differentiating R in each delta gives CD, BC, AD,
or AB, so its componentwise monotonicity claim is also exact.

At the first-sure endpoint, owner0's comparison has affine numerator E2(y)
or E1(x), divided by a positive probability denominator. I independently
verified both identities. The displayed endpoint tests are equivalent to
nonnegativity throughout the stated odds domain, including simultaneous
certainty. A negative individual joining gain is allowed precisely when
the full numerator remains nonnegative. Initially owner0's gap is strictly
negative because its Quit payoff is nonpositive and its Continue output is
positive. Continuity supplies a positive-alpha zero. Both active owners stay
indifferent, quiet3 continues, and the new active owner0 has output Q0<=0.
Thus the constructed root is whole-game Nash at the same continuation.

## 3. Every remaining support and the degree argument

A bad root is proper and has strictly positive output in every coordinate.
The participant bound excludes owner0 from its support. Singleton active
sets have own payoff zero, pair13 has Q1<0, and pair23 has Q3<0. Thus only
pair12 and triple123 remain. The path repairs every bad pair12.

For a triple, positivity of c21,c23 and nonnegativity of b2 give x1<X.
The positive row3 Quit payoff and G>0 give the stated upper bound on x2.
Substitution into the third indifference equation, with the two affine
numerator inequalities, yields v3>0. Hence every positive triple candidate
at that fixed input has x2<Y. The determinant bound follows even when
A=-s+b1 x3 is negative: A>=-s and D,E have the stated upper bounds, while
the positive BCF' term has its stated lower bound.

Eliminating x2,x3 produces a single positive interval in x1. The derivative
of the remaining first equation is det(Dphi)/(DF')>0 throughout, proving
uniqueness. Quiet0 is strict at a bad triple, so its row in Id-T is an
identity row. The other three rows give index -1 by positive diagonal
rescaling of the indifference Jacobian. Under an assumption of no good
root, the repaired pair is impossible and this isolated triple is the only
possible root. Degree normalization on the larger cube gives +1, a
contradiction. No generic perturbation or omitted quiet-owner tie is used.

In particular, the singleton Gamma signs used to perturb bad-pair ties in
the older abstract proof are unnecessary here. They are not secretly used
by the later closed-passive consumer either.

## 4. Complete deviations and semantic coherence

Every behavioral strategy before absorption reduces to an independent law
of its first Quit time, including Never, because the sole live history is
all-Continue play. An entire deviating strategy is consequently covered by
the supremum of all pure-deadline and Never payoffs. The max formula for B'
therefore is an unrestricted cap identity, not a one-step deviation bound.
The payoff/cap maps are 1-Lipschitz in the terminal annotations; composing
arbitrarily many prefixes does not increase that constant.

The passive box contains every actual Never response and is preserved by
all prefix maps. The coherence inequalities follow from decomposing a
player's prescribed law into its original Never mass and finite deadlines.
I checked the displayed residual identity algebraically by expanding
h=(1-q_i)H_i and N'_i=(1-q_i)N_i. Each of its three terms is nonnegative.
Thus coherence is also preserved for the explicitly declared virtual
seeds and on compact closures. Zero debt at positive original Never product
forces U=B=e, so application of the passive bounds at such points is valid.
The proof does not apply them to arbitrary positive-debt intermediate U.

## 5. Adversarial audit of the closed-domain induction

I specifically attempted to break the argument at a degenerate passive
interval, a vanishing seed margin, a nonactual minimum, and a retained-Never
mismatch. None gives a counterexample to the stated proof.

At a nonnegative marked v with only good AllContinue, compactness of the
closed good-root graph makes every nearby good root small. The strict
positive coordinates of v then make all outsiders strictly Continue.
This conclusion concerns good roots only and does not assume bad roots
are small.

In the kernel case, Gamma_SS x=0 makes every core passive first-order term
vanish. Repeating epsilon x for O(1/epsilon) periods accumulates only
O(epsilon) core payoff and cap error: each Quit offer is O(epsilon), and
the passive errors per period are O(epsilon^2). Positive outsiders preserve
their Continue buffers over a sufficiently small fixed survival interval.
The core payoff limit is zero, furnishing the weak marked condition.

In the separator case, w Gamma_SS is strictly positive columnwise, so the
first-order expectation gives wE>=gamma sum q uniformly for sufficiently
small supported roots. The seed z=(1-t)v+t Gamma[:,j] lies in the closed
passive box because each coordinate is a convex combination of allowed
passive values; its j coordinate is exactly zero. No open neighborhood in
that box is required. The initial cap z is expressly virtual. Coherence,
not unproved realizability of the seed, puts later zero-debt minima back
on the same passive diagonal.

The displacement/survival budget c0 is fixed before t is chosen. Therefore
the eventual positive survival loss does not collapse when t tends to zero.
At a seed minimum with survival above1-c0, any nonzero good root preserves
zero debt, the marked condition, and the original weighted inequality,
while lowering survival and retaining strict budget slack. If only the zero
root remains, the positive weighted value forces a proper smaller zero set.
The induction uses roots supported on that subset, hence on the original
set, and retains the ORIGINAL w inequality and survival factors.

An induction endpoint need not itself be an actual finite word. The proof
correctly approximates the selected seed-generated minimum, applies each
fixed finite extension, and chooses the approximation accurately enough for
that extension. Continuous prefix maps and strict survival slack preserve
membership in the original closure. The original terminal cap and payoff
coordinates agree with the induction seed, so changing only its bookkeeping
Never vector does not change those coordinates. The endpoint's retained
Never factors are the original factors multiplied by the extension factors.

Finally, transferring the words from z back to v uses the uniform-in-length
Lipschitz estimate. This removes the virtual seed without accumulated error.
The same finite-prefix approximation argument applies to a global closure
minimum. Thus the local assertion actually supplies the endpoint needed
for the global contradiction rather than only a formal source interface.

## 6. Absorbing repair, global minimum, and fixed target

Moving one owner's original Never mass to a finite deadline makes that
owner's law proper and the resulting profile absorbing almost surely. Its
own cap is unchanged. Four prescribed payoffs and three other full caps
change by at most2M times the moved mass, uniformly over complete deviations.
This proves the14M repair estimate, and continuity transfers its inequality
to closure points. Taking the smallest Never mass gives the stated fourth
root of the joint product.

AllNever is a genuine native zero-debt marked point. If A_Z>0, the repair
estimate forces positive joint Never product at every zero-debt point.
The compact marked zero-debt carrier therefore has a positive minimum.
A proper nonzero good root decreases it; a sure good root contradicts the
repair inequality even if its output is unmarked. Consequently the minimum
is exactly of the local-stall kind. The local assertion produces a smaller
marked zero-debt closure point retaining the original Never product,
contradicting global minimality. This proves A_Z=0.

For an absorbing prescribed profile the original own shift is received in
full; every deviator receives at most that shift because kappa>=0. Original
regret is therefore bounded by native regret. Arbitrarily small terminal
debt supplies the stated fixed-payoff semantic endpoint. The payoff target
is selected before accuracy; no interchange of these quantifiers occurs.

## 7. Exact controls, source correspondence, and coverage boundary

I independently reconstructed the Section7A four polynomials, their endpoint
values and all displayed triple quantities. Its8/5 gains satisfy every raw
condition. The old frozen convexity corner is at most -387/160 for every
permitted f<=1. Section7B's separate-increment control and Section7C's
owner1-first control also pass, including E1(x)=11x/4+5/8 despite g01=-23.
The independent checker additionally exercises simultaneous certainty with
all four quiet-path maxima zero. These are exact rational/symbolic checks,
not numerical root sampling.

I inspected all named source declarations in Section8, including the exact
root/continuation cap max identity, auxiliary Nash debt transport, fixed
terminal-to-uniform endpoint, negative fixed-point determinant obstruction,
and boxed selected-return consumer. Their stated scopes match the packet's
usage. The older boxed consumer does not itself prove the new closed-domain
variant; Sections5--6 supply that variant explicitly. The packet correctly
claims no new Lean check, and I ran no Lean command.

The complete80/65 pattern census,14 withdrawal children, all-weight duals,
role permutations and other prior-producer exclusions require their separate
exact coverage review. I do not count that computation as an independent
part of this review. Subject to that separately recorded coverage evidence,
this packet has a complete mathematical input-to-conclusion proof, with no
unproduced strategic input and no unresolved proof objection.
