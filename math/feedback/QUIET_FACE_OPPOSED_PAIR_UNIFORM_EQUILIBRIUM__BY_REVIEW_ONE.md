# Independent full review: quiet-face repair and the mixed-core cylinder

Reviewer: TRIPLE_CROSSINGS. **PASS for the complete mathematical theorem and
its stated scope.** Ordinary mathematics, not a Lean-checked result.
Reviewed export candidate: `QUIET_FACE_OPPOSED_PAIR_UNIFORM_EQUILIBRIUM.md`,
666 lines, SHA-256
`8fc808db2c7a6e06439719b0d36d71a1002c30d12c2244a78a0d7486c2c7966c`.
I read the whole packet, independently reconstructed its central algebra,
checked the actual-data consumer, and attempted to falsify its boundary and
scope claims. No mathematical objection remains.

## 1. Four independent increments and the finite curvature test

The final main theorem permits unequal d0,d1 and unequal e0,e1. On q3=0,
conditioning on owner 0 gives the exact weighted increments
 d0(1-q2)+d1*q2 and -e0(1-q1)-e1*q1.
The four owner-3 bounds give an upper gap bound. No owner-1 or owner-2
identity when 3 is present is used: the repair stays on q3=0, and every bad
root has q0=0. All four displayed increments are read from the raw table.

At a bad pair, v1<0<v2. Both path denominators are affine and positive at
both endpoints; at tau their lower bounds are -v1 and v2, respectively.
This remains true when d0=0 or e1*tau=c. The complementary hazard numerators
s-d1*alpha and c-e1*alpha verify that all active hazards are proper before
tau, owner 2 is sure there, and owner 1 may also be sure. Both active
indifference equations hold identically. Their limiting denominators may
tend to zero as the bad input approaches an axis, but the proof requires
only positivity at each actual bad pair; no uniform inverse bound is used.

I independently expanded the cubic N and verified its exact second derivative
and endpoint. Clipping only the auxiliary scalar to v3hat=min(v3,60) preserves
initial quietness, since the pair threshold
12x1+(7x1-101)x2<60 follows from x1<=W/c<=5. It raises the upper-gap
polynomial on the entire path. Because e1*d1>=0, its curvature is at least
K(v1,v2)-3f*Delta_d*Delta_e*alpha. That expression is affine in each of the
three box coordinates, so precisely the eight (CVX) corner tests imply
convexity throughout. This includes weak corners, e0 or e1 zero, and negative
f. No passive row-3 bound or extra actual-continuation premise is used.
The endpoint is the displayed positive factor d0*tau-v1 times a function
bounded above by (E). Consequently owner 3 remains quiet throughout.

The scalar f is determined by a finite one-dimensional feasibility test,
not a strategic oracle. The four joining bounds, eight curvature constraints
and the two endpoint tests at v2=0,W are affine half-lines in f, including
the zero-slope cases. The endpoint max expression is exactly equivalent to
those two tests. Unlike the older constant-face case, selecting the largest
allowed joining bound alone is not valid; the final statement correctly
intersects all fourteen constraints.

Owner 0's initial gap is strictly negative. Its final gap is the exact
nonnegative combination (O0), so an intermediate-value zero exists with
0<alpha*<=tau. At an endpoint zero all active comparison equalities still
hold and owner 2 is sure. Owner 0 mixes and has output Q0<=0. This gives a
good whole-game root at the ORIGINAL continuation, including every stated
weak endpoint case.

For equal increments every (CVX) expression reduces identically to 36de>=0,
and (E) reduces to the former constant-face endpoint test. The whole old
class is therefore contained, including e=0. The use of W is only W/c<=5,
so the final ratio bound is sufficient. The one-entry unequal example has
exact minimum curvature values 3531/100 and 7059/200, and endpoint values
-24568/101 and -24468/101, for f=1 and f=1/2 respectively. I recomputed all
four values. With f=1/2 all other nontrivial guards are strict, justifying
independent variation of the unlisted completion entries in a neighborhood.
The numerical core remains fixed; an open sixty-coordinate class is not
being claimed.

## 2. Support exhaustion and the whole real-a corollary

A bad root is proper. Owner 0 cannot be active because of its participant
cap; singleton support has zero active output; pair13 and pair23 have a
negative active output. At negative input minimum AllContinue is not Nash.
Only pair12 and triple123 remain. The repair handles every bad opposed pair,
including a quiet-owner tie.

For a bad triple, v2<=W gives x1<5 and positive owner-3 output gives v3>0.
Every positive triple candidate at those same v2,v3 then has x2<10/11.
The displayed Jacobian bounds and det Dphi>24719/2 are correct. Eliminating
the second and third equations gives one positive interval and derivative
 det(Dphi)/[(4+3x1)(101-7x1)]>0.
Consequently there is at most one bad triple. It is regular, and inactive
owner 0 is strictly quiet. The active gap Jacobian differs from Dphi only
by positive diagonal factors. Its ambient fixed-point index is -1.
The clipped map sends ambient space into the unit cube; homotopy to its
center has no boundary zero on (-1,2)^4 and gives total degree +1. A finite
set consisting only of the identified negative-index roots is impossible.

Section 5 supplies both outer cases without an unproved theorem invocation.
For a<=0, the bad-triple bounds make owner 1's Quit numerator strictly
negative, while pair12 is already good. For a>=1/2 the triple determinant
bounds improve. When a>1/2 the possible bad pair is unique and has index -1;
a perturbation of v3 avoids its sole possible quiet tie. At a=1/2 a
perturbation of v1 avoids its necessary equality v1=0. These perturbations
are available within the closed passive box because rows 1 and 3 have
fixed passive rewards of both signs. They can preserve min v<0, including
at box boundaries. Compactness and the closed good-root graph recover every
unperturbed input. The corollary correctly keeps W<=10 so that its completion
conditions hold with the same remaining coordinates for ALL p>=0 and ALL
real a. It is not a theorem about arbitrary completions.

## 3. Complete semantic consumer

I checked the full-cap recursion (P) and the displayed coherence residual
identity. All terms in that residual are nonnegative. Positive original
Never product and zero debt therefore force U=B=e in the closed passive
box. No assertion that arbitrary prescribed payoffs remain in that box is
used. The proof retains unconditional Never masses rather than resetting
conditional tails.

The local escape induction covers both alternatives. In the nonnegative
kernel case, q=epsilon*x gives O(epsilon^2) prescribed core increments and
O(epsilon) Quit offers. Iterating O(1/epsilon) roots leaves core payoff and
cap errors O(epsilon), while positive outsiders retain their Continue
buffers. In the separated case, the row w may be signed; positivity of
w*Gamma on the positive simplex nevertheless gives (W) for all sufficiently
small supported hazards. The solo-j seed has exact U=e in D and a zero j
coordinate. Its initialized cap is explicitly virtual, which is essential.

The survival budget is fixed before the seed. The displacement estimate
places a hypothetical large-survival minimum in the neighborhood where
selected good roots are small and supported on S0. A nonzero good root
preserves the same weighted fiber and its original survival accounting.
The inequality (1-4delta)(1-c0)>1-eta supplies strict slack. If only
AllContinue remains, the weighted inequality forces a strictly smaller
zero set, so induction applies. Finite extensions are realized in the
original word closure by continuity and a diagonal approximation; no
compact point is executed as an actual strategy. The length-independent
Lipschitz estimate transfers the final words from the moving seed to v.

In the actual closure, moving the smallest Never atom bounds four payoff
changes and three cap changes by 14M*nu^(1/4); the changed owner's cap is
unchanged. This proves (Repair), including at closure points. The minimum
of nu on B=U,min U<=0 is nonempty because native AllNever has zero caps.
If absorbing debt had positive infimum, (Repair) would make that minimum
positive. A nonzero good prefix or the local escape endpoint then lowers
it while retaining zero debt and the marked condition, a contradiction.
Every hypothesis needed by this consumer is proved or explicitly stated.

Finally, an absorbing prescribed law gets its entire nonnegative own shift,
whereas a deviator gets at most that shift. Original regret is therefore
bounded by native regret. The cited terminal-to-uniform endpoint gives one
fixed payoff target before accuracy, against every complete behavioral
deviation. No public correlation, deviation detection, fixed finite calendar,
or shortened response menu enters the proof.

## 4. Explicit falsification attempts and source scope

I tried to break the quiet comparison by taking v3 arbitrarily large. That
attempt exposed an unnecessary earlier cap and led to the clipped-bound
argument now included in the final packet. The actual input remains
unchanged; only a scalar upper-bound polynomial is clipped. I also checked
the simultaneous weak boundary e1*tau=c, both owner-0 joining gains zero,
and E=0. The stated e0=e1=12,f=28 variation satisfies every raw condition.
Its explicit root q=(1/5,1,1,0) has all four gaps zero at every continuation
and the exact stated output. The e0=e1=0,f=-1,
passive-row-3 maximum 1000 variation is also literal and valid. The a=0 and
a=1/2 seams are handled by their own proved branches, not by dividing by a
vanishing coefficient.

I also attempted the incorrect strongest-f shortcut: with s=1/4,c=3,W=5,
d0=11/10,d1=e0=e1=1 and row3 increments all -100, f=100 fails a curvature
corner (-166/5), while f=1 passes with minimum 46 and endpoint -243.
The final fourteen-half-line test correctly handles this nonmonotonicity.
Independent symbolic algebra checked both rational indifferences, the cubic
upper gap, its second derivative, its endpoint, and the constant 36de case.

The literal separating table and its near-zero crossing formulas check
exactly. The safe-edge graph is strongly connected and supplies every
proper marked-set control; the full-marked crossing has strictly positive
output and negative input minimum. Thus selection genuinely differs from
universal marked Nash invariance. I reran the exact fixed-table census:
80 stationary patterns close in 1495 nodes and 65 sure-first patterns in
186 nodes. The independent withdrawal/weight/singleton checker also passes;
all fourteen withdrawal duals and the magnitude-sensitive matrix guards
were recomputed from this table, not borrowed from the prior calibration.
The merged exact checker is `QUIET_FACE_COVERAGE_CHECK_GENERAL.py`, SHA-256
`0bfda0fb7355c124e40a30484efb733ce37a59a0af7af252383b174a63298c59`;
it retains the literal coverage census and adds the symbolic cubic,
eight-corner and unequal-example checks. The separate coverage record
handles the remaining named return/reset selectors. These comparisons do not establish an unrestricted positive gap
or exclude hypothetical strategic extensions of a conditional interface.

The full closed-domain consumer in Section 6 is reproduced from Sections 2
and 5 of the accepted ordinary-mathematical export
`math/exports/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM.md`.
Its restatement is needed for the self-contained packet and is correctly not
claimed as a new consumer. The new raw contribution is the face repair and
its use to cover the opposed-pair parameter strip, completing the stated
unit-gap cylinder together with the two outer cases. The quoted Lean
declarations remain existing conditional interfaces and semantic endpoints;
no new Lean verification is claimed. Arbitrary Fin4 remains open.
