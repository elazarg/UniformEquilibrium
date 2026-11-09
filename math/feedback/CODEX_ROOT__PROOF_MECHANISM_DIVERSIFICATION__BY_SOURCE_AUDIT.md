# Independent review of the corrected singleton-source audit

Verdict: **PASS**, including the native-gap adapter, the complete sign-homotopy
obstruction, and the stronger mixed-pivot-row corollary. This corrects
conjecture-facing coverage; it does not retroactively refute every conditional
variational calculation in the moved packets.

Reviewed [the root note's singleton-chamber source audit](../notes/CODEX_ROOT__PROOF_MECHANISM_DIVERSIFICATION.md#singleton-chamber-overlap-audit).
The section bytes from its heading through before `## Question` have SHA256
`b27980b0047c044319cd728dc41e86699789e1aa71f59bfeb392099782faf15f`.
An independently reconstructed large-axis support census agrees with the
short homotopy proof. This review concerns the displayed proof, not a
numerical sample or a claim of new reward coverage.

## 1. Exact source transfer and degree convention

The checked declaration `quittingSingletonMatrix` uses recipients as rows:
Gamma_ij=R_i({j})-R_i({i}), without negation or transpose. The exact declaration
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` supplies R0 and degree1
from original Fin4 no UE, without an auxiliary-game assumption. These are
static source inspections; I ran no new Lean build.

For an own-zero native Z, finite deadlines tend to the Never payoff. Thus
finite deadlines already have the full native response supremum. In R=Z+1
on nonempty coalitions, every finite deadline adds exactly1, and the limit
of those deadlines dominates R-Never by the nonnegative opponents' joint
Never mass. Hence B_i^R=B_i^Z+1 exactly. Prescribed absorption has probability
1-nu, giving U_i^R=U_i^Z+1-nu and D_R=D_Z+4nu.

Choose an owner whose Never mass is at most nu^(1/4), and move that mass to
a finite date. The owner's cap is unchanged, its payoff changes by at most
2M times that mass, and each other owner's payoff and cap change by at most
2M times that mass. The total error is14M times that mass. This gives
A<=D_Z+14M nu^(1/4). The note's two-case lower bound for D_R is valid and
strictly positive. Its source conclusion concerns R=Z+1; it makes no false
claim that arbitrary terminal-only translations preserve equilibrium.

## 2. Complete sign chamber and homotopy

When the number of negative G_i is not one, the note identifies a literal
nonnegative hollow column and hence a nonzero homogeneous LCP root.

With exactly one negative G_a, the direct homogeneous proof is valid for
all magnitudes, including singular full Gamma. If x_0>0, row0
complementarity forces all observer coordinates to vanish, and row a is
negative. If x_0=0 and x_a>0, row a complementarity forces the other two
observer coordinates to vanish, and either of their rows is negative. If
x_0=x_a=0, their two row inequalities force both remaining coordinates zero.
Therefore the entire strict sign chamber is R0.

The chamber is convex in the literal matrix entries. Along interpolation
to Gamma_old, the complementary map min(x,Gamma_t x) is continuous and
positively homogeneous, and has no zero on the unit sphere. Compactness of
[0,1] times that sphere gives a uniform positive lower bound. Therefore the
usual degree homotopy has one common isolating ball, including after the
fixed offset -one is added. This justifies the sign-homotopy step without
an unspoken nonsingularity assumption.

At Gamma_old, if x_0>0 then row0 gives sum observers=1 and row1 has residual
-2x_0-x_1<0. If x_0=0 then row2 has residual -x_1-x_3-1<0. Thus LCP(-one)
has no root and degree0. Every original table in this chamber is therefore
covered by the existing no-UE=>R0,degree1 contrapositive. The native positive
absorbing-gap source is impossible by the exact adapter above.

## 3. Every strict inverse pivot has a mixed singleton row

The root note correctly applies the established residual matrix filters to
EVERY chosen strict inverse pivot, rather than only one selected pivot.
The pointed normalization H=Gamma diag(Gamma^-1 e_p) preserves signs, degree,
and passive-triple tests and gives H=[0,c;-r,B], r=B1, sum c=1.

For c strictly positive the ten-template argument is exhaustive. In cases1
and2, r_1 and r_2 are negative and pair12 is eligible, so D_12>0. In case3,
if r_2<0 use pair12; if r_3<0 use pair13; otherwise both are positive and
pair23 is eligible. In case4, use pair12 when r_2<0 and pair23 when r_2>0.
These yield D>0, contradicting degree1. The generic row sums are nonzero,
so those alternatives are complete. Cases5,6,9,10 require c_1<0 by a
negative-column condition; case7 requires c_3<0. In case8 the positive child
inverse and c>0 give a strictly positive passive inverse row, triggering
an already available original-game exit.

If c is merely nonnegative, perturb its zero singleton entries upward and
make a further generic perturbation smaller than those newly positive
entries. The positive absorbing gap and the chosen strict inverse column
both persist; all twelve singleton coordinates can be varied independently
while retaining native own zeros. This reduces to the strict contradiction.
Finally Gamma_p(Gamma^-1 e_p)=1 forces some positive off-diagonal row entry.
Thus the row has both signs. No new matrix-coverage theorem is being claimed:
this is a distilled consequence of the existing residual partition.

## 4. Scope correction and repair gate

The withdrawal of the four affected coverage approvals is justified. Their
old Raw chamber cannot represent a positive absorbing-gap source. The
broader generic three-date packet is not restricted to that chamber and is
not invalidated by this audit.

The proposed continuation repair must allow mixed h_i and explicitly retain
both pivot and quiet strict guards. Neither positive Never nor ALL-END gives
nonnegative conditional caps. The root note's two-owner negative-cap control
is consistent with the exact response formulas. A degree1 matrix and an
actual nonminimal guarded profile establish non-vacuity of those conditional
hypotheses only; they do not themselves establish a positive absorbing gap
or supply a minimizing source. Full pre-existing matrix screens remain a
separate admission obligation for any repaired fixture.
