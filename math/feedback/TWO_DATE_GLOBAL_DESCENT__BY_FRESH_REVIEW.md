# Fresh whole review: two-date M14 minima must start with all four owners

PASS for the precise actual-global-minimum exclusions. No unresolved
mathematical objection was found. This is not a UE theorem, a proof that
all finite minima are absent, or a fixed-cap inherited-endpoint repair.

## Exact scope and artifacts

Complete two-date source manuscript, SHA256

    48eb8f3bd21a889184f2b4a22bac9487ced07d339e06ad6ae2e9d0bbc4d892d6

Entire checker `math/experiments/CODEX_NO_CHILD__TWO_DATE_DESCENT_CHECK.py`, SHA256

    15b3c37cf98549e24ec885c00470098dae0035c489d7e90653269c99912f9039

I did not author these constructions, parameter reductions, or interval
certificates. I read the whole final combined proof and complete consolidated
checker. This final review includes the absorbing-face bound and the entire
first012 exclusion; the earlier pair-only review does not supply its approval. I also read the canonical
rational actual-tail construction and attachment formulas in
`math/notes/CODEX_COORDINATOR__FINITE_GLOBAL_DESCENT.md` and the complete
last-root and global first-root arguments in
`math/notes/CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md`.

For the selected source penalty r=m/2, an actual ALL-END exact-observer
positive-Never global minimum with positive caps and exactly two occupied
dates cannot begin with support02 or012. Both possible last supports012
and0123 are exhausted in each case. The first02 argument itself works for
every r>0; the first012 argument uses the proved r<=11/312 bound. Only
(0123,012) and(0123,0123) remain among the prior six endpoint combinations.
No feasibility assertion is made for those survivors.

## Complete parameter reduction and actual feasible selection

Observer0 contact at first02 gives B0_tail=14zF>0 exactly. Thus a last012
root, whose observer0 cap is negative, is impossible. On the complete
full-support last-root branch, positivity of B0 alone selects
alpha<=z<rho0; the established sign partition then gives positivity of the
other three caps as well. The displayed quadratic formula selects that
entire legal branch. I independently checked the exact C0(19/125)>0
identity; monotonicity gives the sharpened upper endpoint. This is not a
numerically selected subbranch.

For fixed last root, zF is fixed. The first observer1 comparison increases
strictly with q0 and reaches contact at the displayed proper positive aF.
All intermediate observer comparisons remain feasible. Observer0's common
cap is 13q2>0; observer1's Continue cap is affine and positive at both
ends of the interval; observer3 and the pivot have positive Continue caps
and nonpositive Quit offers. Thus the entire selection interval is legal.
The complete objective is exactly affine in q0 with formula (5).
At a strict interior comparison, a nonzero slope gives an improvement;
a zero slope permits movement to the contact without changing the minimum.
At contact, decreasing q0 is feasible, so its one-sided derivative gives
r>=R with precisely the displayed sign and positive denominator. This
uses whole-profile minimality, not optimality of the last root.

## Actual tail repair and derivative

The reused rational tail is an actual independent infinite clock profile,
with exact observer optimality, pivot Never optimal, and the stated first-
order caps/survival and quadratic debt. Its construction does not assume
an arbitrary continuation vector. The old last-root pivot gap g is fixed;
C(x(s))=v(s)-g e2 therefore retains all three observer contacts and a pivot
Continue surplus H2 g, including g=0. The last output cap formulas Q_i for
observers and Q2+H2 g for the pivot are correct.

I independently reconstructed the raw P/Q polynomials by enumerating every
coalition of the M14 table. They give exactly the displayed C and all sixteen
Quit derivatives used by the checker. The D inverse, B_i' terms, negative
H2 derivative term, pivot debt derivative, and joint-survival derivative
all match those polynomials. In particular `nu0'=-nu0(1+n.u)` includes the
new tail survival; the zero first-order tail debt contributes nothing.
The first odds repair and hazard derivatives are exact. Differentiating
the full objective (5) gives A+rB exactly, with no missing survival factor.

Positive old caps and proper positive hazards persist for sufficiently
small s, even as a proposed profile approaches the excluded cap boundary.
No uniform lower step size is needed. The first observer0 and observer1
contacts are restored exactly; the other first-root inequalities remain
strict. The competitor changes the whole actual profile and thus prices
the first head rather than treating it as fixed. All finite deadlines and
Never are covered by exact root recursion and the reused tail's full caps;
mixtures price unrestricted private behavioral deviations.

## Exact interval certificate audit

The interval class is sound outward dyadic arithmetic at scale2^80.
Rational endpoints use integer floor/ceiling; addition and negation are
exact at that scale. Products and nonzero-denominator quotients use all
endpoint extrema with outward floor/ceiling, including negative denominators.
Integer square roots give outward bounds. Every used Gaussian pivot interval
is separated from zero. The pointwise exact Gauss-Jordan computation is
contained in the interval calculation despite dependency overestimation;
its final right-hand-side intervals therefore enclose D^-1 k. No residual
approximation or floating inverse is being treated as exact.

Every accepted closed box has strictly negative upper bounds for B and
the required second expression. Failure to establish a sign or a nonzero
pivot triggers bisection; a depth/node exhaustion aborts without PASS.
The two children cover their parent, and the low/high starting intervals
overlap and cover the entire possible z range. Acceptance on some algebraic
points outside the actual admissible branch does not weaken coverage of it.

I ran the checker and reproduced exactly:

- low:73 nodes,37 leaves,depth6, upper bound
  -85607191051274714727/1208925819614629174706176;
- high:51 nodes,26 leaves,depth6, upper bound
  -9151389421230657341/302231454903657293676544.

On the low interval, B<0 and the independently justified r>=R imply
A+rB<=A+RB<0. On the high interval, A<0,B<0,r>0 suffice. Both cases give
a strict actual global improvement. I also reran the canonical last-root
resultant/sign checker and the one-date Bernstein checker successfully.

## Absorbing-face bound and the entire first012 branch

The carrier convention is explicit and correct: C is the zero-observer-debt
subset of the closure of ALL actual augmented tuples, not the closure of
already observer-optimal actual profiles. The finite N-root approximants
with odds t(4,5,1,3)/N therefore need only have observer debts tending to
zero. Their observer passive offers vanish exactly; each Quit offer and
full cap is O(1/N), and the prescribed payoff is O(1/N). Every finite
behavioral deadline is covered, including those after the last root.

For the pivot, Q2 is negative and P2 is positive at each repeated root,
so Never is its full cap. The exact geometric sums have the stated limits:
B2=(11/12)(1-exp(-12t)), U2=(11/13)(1-exp(-13t)), and marginal Never
masses exp(-w_i t). Thus the first limit belongs to C; taking t to infinity
within the compact closed carrier gives nu=0 and debt11/156. This proves
m<=11/156 and the selected r=m/2<=11/312 without executing a continuation
after infinity. It is a specialization of the existing inverse-axis source
construction; the new use is the finite-profile descent below.

At first012, P0<0 and the positive active observer0 contact imply a positive
tail B0. Hence the last root is again the complete positive-cap full branch.
The first observer0/1 equations give exactly the displayed aF(b),zF(b).
I independently reconstructed Q0 and the full pivot objective from the raw
coalition polynomials. They give exactly the Q0 sign polynomial
`5b^2-(18+5v0)b+13v0` after positive denominators are cleared, and
objective(13). Every coefficient in these two expressions is exact.

The small first-odds range is not an unsupported sampling restriction.
The checker certifies v0<1/50 over the whole last-parameter interval; v0 is
independent of b, so obtaining that bound from the rectangular certificate
is noncircular. Positive zF and v0 force b<14/5. Positive current Q0 then
gives the displayed strictly positive quadratic, while its strict upper
bound 5b^2-18b+13/50 is negative throughout[3/200,14/5] by convexity and
the exact two negative endpoint values. Hence every actual first012 point
lies in 0<b<3/200, precisely the certified box.

For fixed last root, aF',zF' and the logarithmic denominator derivative ell
have the stated signs/formulas. The derivative numerator W'-W ell decreases
with r, with coefficient -nu0 ell<0. Checking its strict positivity at
r=11/312 therefore covers every selected source value. I independently
differentiated the quiet3 expression and obtained exactly the checker's
C3' polynomial. The exhaustive two-dimensional certificate verifies its
positivity as well, so decreasing b preserves the quiet inequality even
when it is tied. The other active contacts are preserved exactly, the
pivot continues strictly, and all proper positive hazards persist for a
sufficiently small decrease. The whole actual objective strictly decreases.

The consolidated checker passed all three traversals. Its additional
first012 traversal uses479 nodes,240 leaves,maximum total depth11 and
strict positive lower bound
216680338218802348193/302231454903657293676544.
I checked the refactoring into the common last_root routine and both
consumers; the shared routine changes no formula or interval semantics.

## Empty dates, additional endpoint exclusion, and limits

At an ALL-END source the conditional tail inherits ALL-END, so its cap
is its actual Never payoff. In the first02 branch this forces the positive
last-root caps even if empty dates intervene. During that gap they stay
positive under the constructed repair, so an inserted empty-date solo
Quit0 option is strictly worse than Never. Initial empty dates similarly
see positive whole-profile caps. The appended actual tail starts after the
last original occupied date and replaces the old all-Never continuation.
The argument makes no generic empty-date compression claim on zero or
negative-cap tails.

For first012/last012, player3 is quiet at the first root. Observer0 has
strictly negative passive contribution P0 from the negative singleton1/2
rewards and zero passive12 reward; positive proper hazards make this strict.
Its positive contact value Q0 then forces B0_tail=(Q0-P0)/H0>0, contrary
to the last012 cap. This sign argument is independent of the derivative certificate; the
full last-root branch is excluded by the first012 derivative above.

I attempted falsification through the g=0 endpoint, an omitted last-root
component, sign reversal in r>=R, nonpositive intermediate selection caps,
a wrong joint/deleted survival multiplier, unsafe interval division,
dependence errors in Gaussian elimination, uncovered interval gaps, and
unpriced empty dates. None survives the pinned proof.

Internal retention in the existing finite-descent note is appropriate.
The proof deliberately reuses the canonical classification and actual-tail
construction rather than becoming a redundant standalone export. The exact
root semantics correspond to `quittingTerminalSemanticPair_rootThenContinuation`
and the full behavioral cap recursion in their tracked sources. No Lean
build or formalization claim is made. Longer finite profiles, the two
remaining two-date pairs, infinite sources, and inherited endpoints remain
open.

The complete two-date proof is retained in the second part of [the finite-descent note](../notes/CODEX_COORDINATOR__FINITE_GLOBAL_DESCENT.md). Assembly changed only headings and the checker path; its mathematics is unchanged. The checker is copied byte-for-byte.

## Independent extension review: full first root, triple last root

Verdict: PASS, with no unresolved mathematical objection.

Reviewed addendum: `/tmp/M14_TWO_DATE_LAST_TRIPLE_ADDENDUM.md`, SHA256
`40d18bb4170063e858e27de788b58bbc84d27f5196ff2d0db6a5558df087e136`.
Its source penalty bound is §5 of `/tmp/M14_TWO_DATE_GLOBAL_DESCENT.md`,
SHA256 `48eb8f3bd21a889184f2b4a22bac9487ced07d339e06ad6ae2e9d0bbc4d892d6`.
This review covers the complete short addendum and its use of that bound;
it does not reapprove the separate first02/first012 interval checkers.

I independently checked the following exact identities and implications.

1. At the full first root, positive whole observer caps and zero observer
   debt force Q0>0 and Q3>0. In odds(a,b,t,y),
   Q0=-5+(5+18t)/[(1+b)(1+t)(1+y)] and
   Q3=-5+(5+18b)/[(1+a)(1+b)(1+t)]. These imply the two stated strict
   product bounds and therefore nu_first>25/324. No tail-cap positivity
   is used; in particular the negative last observer0 cap is allowed.
2. At last support012, the observer contacts give
   a=6Z/(14-5Z), b=14Z/(4+5Z), with 0<Z<14/5. The remaining quiet condition
   is 70Z^2+2980Z-2264>=0. This polynomial is increasing for Z>=0 and its
   value at74/100 is -5117/250, verifying Z>=z_*>74/100>1/2 directly.
3. The pivot debt is exactly
   [Z/(1+Z)](6a+7b+5ab)/[(1+a)(1+b)], which simplifies to the stated
   Z^2(1516+110Z)/[(14+Z)(4+19Z)(1+Z)]. All denominators are positive.
   Twice its numerator minus its denominator is
   201Z^3+2743Z^2-326Z-56. For Z>=1/2 it exceeds
   201Z^3+(2091/2)Z-56>=3935/8>0. Thus d_tail>1/2 on the entire branch.
4. ALL-END gives the exact debt recursion
   d_first=q2(e2_first-Q2_first)+nu_first*d_tail. The first term is
   nonnegative. Adding r*nu_total preserves the lower bound, so
   mu>25/648. The strict numerical margin is
   25/648-11/312=7/2106>0, contradicting mu<r<=11/312.
5. The penalty bound is correctly on the augmented semantic absorbing face.
   Its independent inverse-axis approximation gives limiting pivot cap11/12
   and prescribed payoff11/13, hence debt11/156. It does not treat the
   finite approximate-observer profiles as exact observer equilibria.
6. Empty physical dates are retained. Their joint survival is1 and their
   pivot debt contribution is zero under ALL-END, so no deleted Quit0 option
   enters the comparison. All caps used are full behavioral caps; no
   response-class restriction or strategy construction is introduced here.

The argument eliminates the entire stated actual first0123/last012 mode.
Together with the separately reviewed first02/first012 exclusions, it leaves
only full/full two-occupied-date actual minima. It does not exclude that
remaining class, all finite minima, inherited non-actual points, or Fin4.

The reviewed addendum is retained as the final section of the canonical finite-descent note, changing only its heading.
