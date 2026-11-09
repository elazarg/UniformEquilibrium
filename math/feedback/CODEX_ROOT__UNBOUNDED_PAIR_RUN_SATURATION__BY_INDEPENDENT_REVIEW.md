# Independent audit of the four-run saturation chart

Reviewer: run_chart_review, independent of the theorem's construction.
Reviewed artifact: [the retained run theorem](../notes/CODEX_ROOT__UNBOUNDED_PAIR_RUN_SATURATION.md),
SHA256 811661e7579fe534adfed5011db90e8f945ad41d3af742fb1078875efc268f6d.
The final ownership/status header was inspected against the fully reviewed
proof; the mathematical body is byte-identical.

Verdict: mathematical PASS for the stated ratio-chamber theorem. The proof
really handles unbounded physical run lengths; it does not infer uniformity
from the earlier fixed-window inverse function theorem. No Lean check ran.

## Exact run law and reduced coordinates

I independently derived the finite deadline differences. Since every active
observer atom is an optimal response, its successive deadline offers agree,
forcing alpha_(t+1)=(1-G_i/J_ip)alpha_t and alpha_0=E_i/J_ip.
The total pivot mass and all three first-coalition probabilities are the
displayed exact expressions. In particular their sum is f+g-fg, and the
Never-coordinate forward map is correct for all four owners.

The argument needs E_i/J_ip>0, not E_i>0. The ratio conditions supply
0<lambda_i<1, positivity of f, and all z_ij>0 even when some G_i are negative.
The observer row-sign generalization is therefore sound. It does not claim
that multiplying a player's rewards by a negative number transports an old
equilibrium or its strict quiet inequalities.

Holding normalized observer atoms fixed and varying their total mass is a
legal complete-law operation. Scaling the geometric pivot atoms likewise
keeps every original supported date positive on a small two-sided interval.
All moments and length parameters enter a fixed finite analytic map. Their
compactification includes theta=0 only as an analytic limiting parameter;
no infinite run is executed or placed before a later finite date.

## Uniform inverse and exact feasibility

Replacing the last active observer's terminal-cap constraint by its last-run
entrance-cap constraint is exact: that coordinate's forward map depends
only on its entrance cap and theta, independently of the observer mass.
This is the essential correction for long last runs.

I independently checked the kernel calculation. The last entrance equation
gives Gamma_l x3=0, hence x4=x3-e_l u4. The other three terminal equations
then force x4=0 by invertibility of Gamma. For labels i,j,k,i, the remaining
coefficient is z_ki+theta_k z_ji; for i,j,k,j it is z_kj. Their displayed
strict lower bounds hold uniformly over the closed parameter cube. The
first and last theta values do not create an omitted degeneracy.

As an exact symbolic check, for the star singleton matrix with G_i=2 and
observer cross entries -1, the two reduced determinants are respectively
3(theta2 theta3-1) and -3(theta3-1). This agrees with the kernel proof,
including every theta=0 boundary. The moment parameters do not enter this
zero-data derivative.

A compact parameter set, a uniform nonsingular derivative, and uniformly
bounded analytic derivatives give the claimed fixed-dimensional charts.
All actual entrance data and run masses tend uniformly to zero at late
cuts: each is bounded by a constant times that actual law's remaining
conditional finite mass, uniformly over every later cut. The last entrance
target used in the reduced constraints obeys the same bound. Thus there is
no hidden dependence on a growing number of dates in the derivative limit.

The feasible interval itself need not be uniform. Each chosen four-run
window is finite, so all its positive supported atoms and strict quiet/pivot
inequalities survive on some two-sided interval. The unchanged literal tail,
exact active contacts, and backward full-cap recursion price every complete
deviation. Earlier observer entrance payoffs and caps stay fixed; every
earlier pivot deadline stays below the changed END on a smaller interval.
This uses absence of any finite pivot cap attainer, exactly as stated.

## Limit and scope

The aggregate payoff and survival maps use only four outcome triples and
the fixed continuation. Their first derivatives are uniformly controlled.
The entrance and terminal equations imply Gamma a_total=e_p, including
at the compactified parameter boundary, hence derivatives 1 and -S.
The whole-objective derivative has the correct distinct survival factors.
Actuality and positive original Never then give the claimed saturation
identity, with no weak-limit mass relabeled Never.

The run combinatorics is correct: an infinite adjacent-distinct word using
all three labels infinitely often has arbitrarily late distinct triples,
and the following label is one of the first two. Those four-run windows
need not have any fixed physical length.

This is a strict extension of the prior fixed-window source restriction.
It leaves global minimum realization, finite pivot contacts, equality,
quiet ties, other ratio chambers and other support geometries open.
The theorem itself proves no new raw reward-table UE class. Conditional
source-mode significance is supported, but final export admission would
require a self-contained packet and its exact-source/overlap audit.

## Appended one-negative boundary example

The appended fixture is also approved at the hash above. I independently
checked det Gamma=6, the inverse pivot column (1/3,1/3,1/3,1/3), det F=1728,
the entrance/exit matching equation, and all four leading gap vectors.
The finite IFT family and its summable concatenation give an actual tail;
assigned offers tend to zero, so no actual tail values are assumed circularly.

I recomputed all four prefix END offers and Quit offers. The displayed
participant triples make observers2,3 exactly indifferent. Observer1's
Quit offer is -51/8, and the pivot's gap is exactly -h. The new passive
pair/triple coordinates cannot occur in the pair-only tail's actual outcomes;
the participant triples that can enter its quiet deviations only lower
their values. Thus they preserve that actual tail, rather than requiring a
new circular IFT construction after the table changes.

The prefix makes every entrance cap positive, keeps all full observer caps
exact, preserves strictly positive original Never, and leaves every pivot
finite deadline strictly inferior. Tail pivot debt is O(h^2), prefix pivot
debt is h/2+O(h^2), and root joint survival is1/8. The stated r=1/4 strict
mass and J_r<r bounds follow. This example has bounded runs; it is not
presented as a construction of an unbounded-run global minimum.

The all-positive orientation's negative determinant follows from the
negative determinant of its observer block and Schur complement1/v_p>0.
The positive-gap native source requires det Gamma>0, as proved in PartII
of [the strict-column source theorem](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md). The new
one-negative fixture correctly avoids that particular solved orientation,
without claiming exclusion from every other UE criterion. The missing
global minimum and positive absorbing gap remain explicit.
