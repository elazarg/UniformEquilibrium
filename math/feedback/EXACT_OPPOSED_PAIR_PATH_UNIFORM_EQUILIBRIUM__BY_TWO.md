# Second independent review: exact opposed-pair path UE theorem

Reviewer: FIBER_REVIEW. Ordinary mathematical review; no Lean build.

Complete reviewed packet: `math/exports/EXACT_OPPOSED_PAIR_PATH_UNIFORM_EQUILIBRIUM.md`.
SHA256: `d7f3fdd20419800f8e5150c5e512129a24e97ebdc365645acd68fa8f493967bf`.

Verdict: PASS. Sections1--8 form a complete proof of the stated raw
four-player UE criterion, including the actual-data strategy consumer.
No unresolved mathematical objection. The theorem does not settle arbitrary
Fin4 and does not assert Lean verification. Its exact four-polynomial tests
characterize the stated path envelope, not all actual continuations or UE.

## 1. Direct root geometry and exact elimination

At a proper bad pair12, indifference gives v1=-s*x<0 and v2=c*y>0.
With A=sx+d0*alpha, B=cy+e0*alpha, C=s-d1*alpha, D=c-e1*alpha,
A,B are strictly positive at every actual pair throughout the path, including
d0=0 or e0=0. C,D are nonnegative by the definition of the first endpoint
tau. Therefore the path denominators stay positive and its hazards remain
proper before tau. Both active gap identities follow by substitution.

I independently reconstructed the quiet3 gap by conditioning first on
owner0. With0 quiet it is

    l*q1*(1-q2)+m*q2*(1-q1)+n*q1*q2-v3*(1-q1)*(1-q2).

With0 quitting it is the independent expectation of the four actual delta
entries. Clearing the displayed positive denominator gives N_v exactly.
The original quiet comparison says v3>=ly+mx+nxy. Since CD>=0, substitution
of that lower bound gives an upper bound for the gap. Its factor alpha*R
and every coefficient r0,r1,r2 are correct. Thus no continuation cap,
correlated action, or substituted reward assumption is hidden in this step.

The finite quadratic maximum test is exact. When the leading coefficient
is negative and the vertex is interior, p(vertex)<=0 is equivalent to
4da-b^2>=0; the direction uses d<0. Endpoint, linear, constant and
boundary-vertex cases are all included. Multiaffinity in x,y proves the
four-corner equivalence. On x>=0, constant and slope must both be
nonpositive, which proves the unbounded version. The x coefficient has
degree at most1 in alpha, as claimed.

Corner hazards may be undefined when x or y is zero and a denominator
vanishes. This causes no gap: the finite tests are polynomial statements;
the actual root construction always has x,y>0. The packet explicitly
restricts the necessity assertion to the binding-continuation envelope.

The derivative of R with respect to each delta is CD, BC, AD or AB.
All are nonnegative on the path. Decreasing one actual joining increment
therefore improves the envelope, and maximal permitted f is valid if a
common scalar relaxation is chosen. This does not assert monotonicity of
the older sufficient curvature inequalities.

## 2. Endpoint comparisons and complete support exhaustion

At alpha0 owner0 strictly prefers Continue because its output is positive
and all its participant rewards are nonpositive. At C(tau)=0 its exact gap
is [g02*D+g012*B]/(B+D); at D(tau)=0 it is
[g01*C+g012*A]/(A+C). These are the stated E2 and E1 numerators.
Finite endpoint tests are exact by affine interpolation; on an unbounded
x interval the constant and slope conditions are exactly the stated ones.
If both players become sure together, both comparisons reduce to g012>=0.
Thus one individual joining gain may be negative without invalidating the
argument. The intermediate value zero occurs at alpha*>0, makes all four
comparisons Nash, and gives active owner0 output Q0<=0.

I checked the remaining-support argument independently. A bad root cannot
activate0. Singletons have native own output0; pair13 has Q1<0 and pair23
has Q3<0. The remaining pair12 is repaired. At a bad triple, its positive
row3 Quit payoff implies the displayed bound on x2. Substitution into phi3
and the two affine a_star guards give v3>0. At that same continuation all
positive triple candidates satisfy x1<X and x2<Y.

For the derivative matrix

    [0,A,-B; C,0,D; E,-F',0],

the determinant is ADE+BCF'. Its bound by Delta is valid even when A is
negative: A>=-s, D and E have the stated upper bounds, and B,C,F' have
positive lower bounds. Eliminating phi2,phi3 leaves one interval and
derivative det(Dphi)/(D*F')>0. Hence at most one bad triple exists.

The ambient degree argument includes the inactive coordinate correctly.
Quiet0 is strict, so its row of Id-T is an identity row. The three active
rows have the negative of a positive-diagonally-scaled Dphi. Their index
is -1. If there were no good root, every fixed point would be this one
regular triple; the clipped-map homotopy gives total degree+1, a
contradiction. No generic perturbation is needed.

The previously used singleton Gamma sign assumptions are unnecessary here.
Pair ties are repaired directly, and the closed passive consumer below
uses no interval-interior assumption. W=0 and H=0 are handled by absence
of the relevant bad support, without dividing by a zero bound.

## 3. Full review of the reproduced actual-data consumer

The first-Quit-law model covers all unilateral behavioral replacements:
before absorption the only live history is all-Continue. The exact prefix
cap is the maximum of quitting now and continuing to the full tail cap.
The U, B, e, N recurrences and the nonnegative residual decomposition
are correct. At zero debt with positive Never product they force U=B=e
in the closed passive box, including for compact limits.

The local small-hazard induction is complete. In the nonnegative kernel
case, P_i and E_i on the zero set are O(epsilon^2), while Q_i is
O(epsilon); repeated prefixing controls all caps uniformly by O(epsilon)
over O(1/epsilon) dates. Positive outsiders retain Continue buffers for
fixed small total hazard. In the separated case the signed row w has
strictly positive columns, giving wE>=gamma*sum q for all small supported
hazards. The solo-column seed lies in the CLOSED passive box even if the
box has degenerate intervals. Its cap initialization is explicitly virtual.

The budget and displacement estimates put every hypothesized seed minimum
within the neighborhood where all good roots are small and use only the
current zero set. A nonzero good root preserves the weighted original
inequality and decreases survival within the budget. Otherwise the sole
good root is AllContinue; its zero set is proper because wU>0. The
induction endpoint lies in the same minimizing closure by approximation
of each finite extension and strict survival slack. This yields the stated
contradiction. Finally, nonexpansiveness removes the virtual seed without
accumulating an error proportional to word length.

For the global marked minimum, moving a smallest ORIGINAL Never atom
changes four payoffs and three other caps by at most2M times that atom;
the mover's own cap is unchanged. This proves the coefficient14 in the
repair bound. A positive absorbing debt infimum forces positive minimal
Never product. Applying the local construction at that SAME source lowers
the product within its actual annotation closure, contradicting global
minimality. No assumption of actual attainment by one profile is used.

An absorbing prescribed native profile receives the full own offset in
the original game, while a deviator receives at most that nonnegative
offset. Native small debt thus bounds original regret. The named semantic
endpoint fixes a payoff before the requested accuracy. There are no missing
strategic input premises, public randomization assumptions, conditional-tail
resets, or bounded-deviation restrictions.

## 4. Exact controls, coverage and falsification attempts

Reran `/tmp/GENERAL_FACE_GEOMETRY_CHECK.py`, SHA256
`0e61b2dc02380eb72ef8e252b30dd54cef67355bbf83a7fae1560cf4d4f67fac`.
All symbolic identities and all three displayed boundary controls passed.
Also independently reconstructed the conditioned quiet gap and the triple
Jacobian/elimination identity rather than relying only on the author's
factorization. A concave quadratic -1/10+t-t^2 demonstrates why endpoint
tests alone would be false; the packet's vertex condition rejects it.

For Section7A, d0=e0=1,d1=e1=8/5,delta=-1 and tau=5/32 follow from the
literal rewards. Every quoted endpoint value and every positive triple
quantity is exact. The old convexity corner is
-21/5+(57/32)f<=-387/160 for all permitted f<=1. The numerical labeling
is forced by the fixed core; its unit-gain corollary also fails. The new
criterion therefore supplies a genuine extension of that frozen producer.

Reran `/tmp/EXACT_FACE_EIGHT_FIFTHS_COVERAGE.py`, SHA256
`02b4b8888edf44f53920a4ce5f20f6babaa28d1f527ae12520790e453cb679ca`.
Results: all80 stationary patterns excluded in1343 subdivision nodes;
all65 sure-first patterns excluded in162 nodes; all reported legacy
withdrawal/weighted/return/reset/matrix and marked-invariance assertions pass.
I checked the complete 3^4-1 stationary pattern enumeration, pure and
single-mixer cases, inverse-Gamma origin exclusion, rational Bernstein
subdivision and sign logic. For the sure-first census the sure owner's
cap is lower-bounded by L, while every other player's H vanishes; hence
its tests include arbitrary actual punishment tails, not one selected tail.
All comparisons are rational and no node remains unresolved. Detailed
definitions of the older named producer families remain in their separate
coverage audit; this review does not claim a census of all possible proofs.

The delta00=150 control checks that a single positive joining difference
can be harmless even when every common scalar relaxation fails. The
e0=e1=16 control checks the OTHER first-sure endpoint and the negative
g01=-23, with E1=11x/4+5/8>0. Their claimed scope is correctly limited to
path controls rather than separate complete prior-producer exclusions.

## 5. Source audit and export boundary

Inspected the named prefix cap, auxiliary debt, selected negative-index,
ambient degree and terminal-to-fixed-uniform-payoff sources. The quoted
declarations exist and their hypotheses match the roles assigned to them.
The boxed selected-return source is correctly identified as having a
different domain; the packet reproduces the needed closed passive/sure
variant in full rather than silently invoking a stronger Lean theorem.

The packet has no reference to a temporary or conference math file as a
mathematical dependency. Its inherited ordinary consumer is reproduced,
and the remaining references are named Lean interfaces and standard
finite-dimensional Nash, separation, compactness and degree facts.
No fresh Lean check is claimed. The prior-producer checks concern named
families and a literal table; they are not a positive exploitability gap.
