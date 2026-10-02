# Joint conditional-tail restart and the complete repair rows

Identity: CODEX_TARSKI_PREMIUM.

Status: bounded ordinary-mathematics test stopped; research paused at the
user's request. The actual conditional-law operation and its complete
response/LP identities are proved below. They do not produce a strict
global repair-value decrement. Once every response is retained, the proposed
selection falls within the existing independent-recombination envelope.
No new selector, source impossibility, Lean claim, or export is asserted.

## 1. Source, operation, and narrow overlap check

Fix a canonical four-player quitting table: own singleton rewards are
(1,0,0,0), all-Never pays zero, and all rewards have absolute value at most M.
The complete behavioral regret objective is E, its GLOBAL infimum is m,
and R(q) is the infimum of E over every pivot law against the three actual
independent finite opponent laws q=(q_1,q_2,q_3).

Work hypothetically with m>0 and actual profiles p_n=(pi_n,q_n) such that
E(p_n)->m. Hence m<=R(q_n)<=E(p_n), so R(q_n)->m. The checked MAX-tie
theorem gives every actual debt d_i(p_n)->m through compact semantic-pair
subsequences, not convergence or attainment of the clocks. These source
facts are justified in the preceding
[two-deletion note](CODEX_TARSKI_PREMIUM__TWO_DELETIONS_OF_ONE_PAIR_AND_MAX_TIE_DISPATCH.md).

The proposed joint operation selects a deterministic cut K and independently
conditions EACH nonpivot's original law on T_j>=K. Write

    s_j=P(T_j>=K),       P=s_1 s_2 s_3,
    q_j^+=(law of T_j conditional on T_j>=K).                 (1)

Only cuts with all s_j>0 are admissible. Never belongs to the conditioning
event and its new mass is q_j(Never)/s_j. The three new laws remain
independent. Their clocks keep their ORIGINAL date labels, including all
silent dates before K, and the pivot is reoptimized completely.

Retaining those dates matters. Collapsing every old pivot time below K to
one new first date could let a nonpivot join all that pivot mass in one
response. That is not the present operation or an innocuous relabeling.
The selected operation really removes early opponent atoms and renormalizes
their own remaining laws; it does not merely change a description's cutoff.

The relevant earlier tests were read before the calculation:

- RENY's [full active-response recombination](CODEX_RENY__SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY.md)
  retains all independent cube corners and every newly exposed response.
- NOETHER's [complete joint repair envelope](CODEX_NOETHER_SUPPORT__JOINT_OPPONENT_MOVE_AND_COMPLETE_REPAIR_VALUE.md)
  requires ALL optimal LP duals for a directional upper comparison.
- FRECHET's [exposed-cap tail selection](CODEX_FRECHET_CYCLE__KKT_CORNER_EXPOSED_CAP_EXACT_TAIL_SELECTION.md)
  optimizes one free tail behind a sure owner, leaving the other caps
  invariant. It is not the joint conditioning in (1).
- FRECHET's [first-solo rotation](CODEX_FRECHET_CYCLE__FIRST_SOLO_HAZARD_ROTATION_AT_GLOBAL_MINIMUM.md)
  retains literal tails and a fixed joint continuation factor; its available
  late-response lower bound does not assert a conditional-restart theorem.

The first two sources turn out to delimit the present operation too.

## 2. Exact original-response identity, including deleted Never

Fix ANY actual pivot law pi, without optimizing it yet. All expectations in
this section use the same independent original clocks (pi,q). Put

    A={T_1>=K,T_2>=K,T_3>=K}.

For owner i and any complete pure response ell (finite time or Never), let
F_i be its original realized reward, with zero on all-Never, and let
F_i^ell be its realized reward when its own clock is replaced by ell.
Define the bounded signed kernel Z_i,ell=F_i^ell-F_i.

Conditional on A, the original four clocks have exactly the product law
(pi,q^+). Therefore the FULL pure gain satisfies

    g_i,ell(pi,q^+) = E[Z_i,ell 1_A]/P,
    P g_i,ell(pi,q^+) = g_i,ell(pi,q)-C_i,ell(pi),
    C_i,ell(pi)=E[Z_i,ell 1_(A complement)].                 (2)

This is not conditioning the deviator's chosen time on survival. The event
A refers to the original independently sampled clocks. When i is a
nonpivot, its old sample is ignored by F_i^ell, which gives the exact factor

    E[F_i^ell 1_A] = s_i E[F_i^ell 1_(A_-i)],
    A_-i={T_j>=K for nonpivots j other than i}.               (3)

Consequently the response denominator is P/s_i whereas prescribed payoff
uses P. The pivot response denominator is P. Equation (2) incorporates
these different factors; substituting P for every deleted reach before
including s_i would be incorrect.

No absorption is assumed. On the event that all relevant original opponents
choose Never, a finite response still receives its own singleton, while
Never receives zero. Those outcomes are part of F_i^ell in (2). Thus the
pivot's after-menu singleton term is present, and the corresponding
nonpivot term vanishes only because its own singleton is zero.

If q has all finite dates below N, q^+ uses a subset of the same dates.
Every integer response, including unused and joining dates, remains allowed.
The complete pivot-repair LP can use its ORIGINAL deadline N and all its
head, Never, first-late, and limiting-late rows. There is no calendar or
late-test identification across different sources in this operation.

## 3. Complete pivot optimization does not remove the signed correction

On that fixed deadline, let x range over the compact feasible pivot mass
polytope and let a range over ALL affine repair constraints, including the
zero row and every owner's full response endpoints. Write

    R(q)=min_x max_a g_a(q,x).

Let C_a(x)=g_a(q,x)-P g_a(q^+,x). These are affine functions of x. For
actual geometric/finite pivot realizations they are the corrections (2)
at the relevant responses or their bounded late limits. The identity
extends to the zero-first-atom LP boundary by continuity of its affine
coefficients; it does not assign that boundary a fictitious actual law.
The exact behavioral-infimum theorem then gives

    P R(q^+) = min_x max_a [g_a(q,x)-C_a(x)]
             = max_beta min_x sum_a beta_a[g_a(q,x)-C_a(x)], (4)

where beta ranges over the entire simplex of complete repair rows.

In particular, for ANY old optimal dual beta,

    P R(q^+) >= R(q)-max_x sum_a beta_a C_a(x).              (5)

Proof: old dual optimality gives sum beta_a g_a(q,x)>=R(q) for every
feasible x. Subtract the largest possible correction and minimize. This
is a LOWER comparison; selecting one favorable old dual cannot reverse it.

For one old optimal primal x, write its row slack as
b_a(x)=R(q)-g_a(q,x)>=0. It supplies the valid upper comparison

    P R(q^+) <= R(q)-min_a [b_a(x)+C_a(x)].                  (6)

The minimum ranges over all rows, including old inactive rows and zero-
weight rows. Exact pivot reselection may improve (6), but is already fully
allowed by (4). Neither all four source debts tying nor one old optimal
dual implies that the right side of (6) is below P R(q), let alone below
P[R(q)-delta] for a fixed cofinal delta>0 when m>0.

The remaining unpriced expression is thus the signed removal correction
C_a on the event that at least one nonpivot quits BEFORE K, with the
different deleted factors in (3). It is not solely the mass of a hidden
late pair.

## 4. Why the common-clock relocation does not close this operation

For a hidden pair {a,b} and complementary owners 0,j, the preceding note
proves D_0 D_j<=q_pair X. If X_n->0 and D_0,n stays positive, it follows
that the complementary observer's near-cap gain has contribution m-o(1)
from OTHER deleted coalitions/timing terms. That statement uses the same
actual source and the complete response class.

It gives no sign for C_j,ell in (2). A relocated gain may be earned by
joining an early pivot, through an early singleton or another coalition,
or after K through a different opponent coalition. The event A complement
partitions by whether the ORIGINAL nonpivot clocks quit early, not by which
deleted coalition supplies that gain. Likewise the pivot and the other two
owners have their own signed corrections. None can be dropped from (4).

There is an exact relation to the old recombination boundary. For s_j<1,
let q_j^- be its law conditional on T_j<K; then

    q_j=(1-s_j)q_j^-+s_j q_j^+.

The eight head/tail patterns are actual independent product laws. For each
fixed pivot x and complete row a,

    g_a(q,x)=sum_pattern weight_pattern g_a(q^pattern,x).    (7)

Zero-weight patterns need no conditional law. If s_j=1 only its tail
branch is used. Thus (2) is one selected corner of the already known
independent three-law recombination identity, not a new convexity property
of R. Although every positive-weight pattern satisfies R(q^pattern)>=m,
their optimal pivot masses and optimal duals need not match. A fixed dual
only gives lower certificates, as in (5). Equation (7) cannot select a
corner with smaller MAX regret by averaging signed gains or owner debts.
No such minimax interchange is being used.

One elementary whole-operation bound is useful only for stopping scope:

    |R(q^+)-R(q)| <= 4M(1-P).                              (8)

Indeed the original opponent product law conditioned on A has total
variation distance 1-P from the original law. For any fixed pivot law,
prescribed payoff changes by at most 2M(1-P). A pivot response has the same
bound. A nonpivot i response changes by at most
2M(1-P/s_i)<=2M(1-P), since its own marginal disappears. Taking response
suprema and the pivot infimum proves (8), with no attainment needed.
Consequently cuts with 1-P_n->0 cannot give a fixed decrement. This is
only a quantitative boundary on the chosen operation, not a new locality
no-go theorem or a denial that macroscopic joint law changes may work.

## 5. Exact status and parked question

Proved: the actual independent conditioning operation; full response
identities (2)-(3); complete LP comparisons (4)-(6); the eight-pattern
identity (7); and (8), including the after-menu and Never boundaries.
The prior common-clock covariance inequality is preserved and not modified.

Unproved: any implication from a genuine positive global infimum to a cut
and a new feasible pivot mass making EVERY corrected row in (4) uniformly
smaller. The relocation does not supply it. The operation has reached the
already documented complete-recombination upper-comparison boundary and is
stopped, not promoted as a conditional compiler. No solved-table/local-tie
example is substituted for the hypothetical global source.

One concrete question retained for a future, distinct test is whether an
actual joint opponent change can exploit the original near-cap response
OUTSIDE the hidden pair while changing the conditional tail laws themselves,
rather than selecting one of their existing eight head/tail corners. Any
such test must price the complete corrections for all four owners and allow
a new pivot optimizer. No such next operation is selected or begun during
the requested pause.

Source route: the current pivot-repair paragraphs of `docs/FRONTIER.md` and
`docs/TOOLKIT.md`; `exists_objective_minimizer_eq_behavioral_infimum` in
`Quitting/Terminal/PivotRepairBehavioralInfimum.lean`;
`singlePivotFiniteMenuScalarSource_iff_smallPivotRepairValue` in
`Quitting/Terminal/SinglePivotRepairSourceEquivalence.lean`; affine complete
constraints in `Quitting/Terminal/PivotRepairFiniteLP.lean`; and the
all-player MAX-tie and pure-time cap sources cited in the preceding owned
two-deletion note. The earlier exact LP sources were rechecked through this
route; their opponent-selection hypotheses are not taken as conclusions.
The separately announced cross-mass determinant and dirty reward-exclusion
source are not used here.
