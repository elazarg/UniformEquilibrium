# Independent review: membership stretch and the singleton-only source

Reviewer: CODEX_TARSKI_PREMIUM.

Reviewed source:
`notes/CODEX_NOETHER_SUPPORT__MEMBERSHIP_STRETCH_AND_SINGLETON_BOX_SOURCE.md`

SHA256:
`7063965c31fa04fb0c5755f298a329a466f9e0054cb8abb84a423169c67e4a54`.

## Verdict and scope

PASS on the stated ordinary-mathematics reduction and its actual source
construction. I reconstructed the stretch and restricted-source argument
from the task statement before reading the candidate, then read all 348
lines of these frozen bytes. I did not read FRECHET's parallel review.
No mathematical repair is requested.

Conditional on a positive worst Fin4 value, the argument produces a fixed
56-coordinate family with four freely variable own singletons, a positive
restricted maximum Ω_b, and a uniform strict separation between Ω_b and
the full regrets of ALL eleven nonsingleton sure-coalition profiles. It
then produces actual near-minimizing silent sources, one common family of
near-active weights with enlarged-domain control and all-owner positive
mass, and the total singleton-pressure sign.

It does NOT retain the original sixty-coordinate cube normal, show descent
of actual exploitability, prove that Ω>0, or produce a uniform equilibrium.
The source explicitly preserves these limitations. No Lean seal is given.

## 1. The sure-profile formula is the complete behavioral formula

Fix |S|≥2, with every member Quit0 and every outsider Never. Removing any
member's own clock still leaves a sure date-zero opponent. For a member,
every response continuing at zero therefore receives r_i(S\{i}); for an
outsider it receives r_i(S). Quitting at zero gives the other endpoint.
There is no earlier action, and every randomized or behavioral response
averages those two endpoints. Thus

    E_r(p^S)=max_i [r_i(S△{i})−r_i(S)]_+

is exact against all original responses, not merely a root-game regret.
The grand coalition is covered. Singleton S is deliberately excluded:
removing its sole quitter would expose a continuation and the displayed
two-endpoint argument would no longer apply.

None of these directed toggle coordinates is an OWN singleton. In the
only apparent boundary case, S\{i}={j}, one has j≠i. Hence varying the four
own singletons leaves all eleven sure regrets exactly fixed. There are
6+4+1=11 such coalitions.

For each owner, the seven pairs (B,B∪{i}), nonempty B⊆I\{i}, partition
its other fourteen reward coordinates. These pairs do not conflict with
another owner's pairs, because reward coordinates are owner-indexed.
The same stretch therefore handles all eleven profiles simultaneously.

Every positive directed difference c becomes (1−α)c+2α; every negative
one remains negative, and an equal pair stays equal. When e_S>0, taking
the maximum commutes with this common increasing affine map. This proves
the source's exact transformation (6), including α=0 and α=1. The positive
premise matters: an all-zero table remains zero under the specified
equal-pair convention, rather than acquiring regret 2α. The source obtains
that premise from Γ(r*)≥η(r*)=Ω>0, so no boundary gap is present.

P(r) can be discontinuous at equal pairs. The proof stretches one FIXED
r*, and never differentiates P or requires its continuity; this causes
no problem in the subsequent optimization.

## 2. Positivity and strict separation survive the parameter change

For any fixed actual profile and response, raw reward distance δ changes
the terminal expectation by at most δ, including the unchanged zero Never
outcome. Every gain changes by at most 2δ. Taking arbitrary response suprema,
player maxima, and then the infimum over actual independent profiles
preserves the same 2-Lipschitz bound for E and η. No cap attainment or
limiting strategy is needed for this argument.

The all-Never profile has full regret max(0,max_i s_i), so η≤1 throughout
the unit cube. Thus a worst table exists and 0<Ω≤1 under the hypothesis.
For 0<α<Ω/8, the stretch moves the table by at most 2α and gives

    η(r*_α)≥Ω−4α>Ω/2,
    Γ(r*_α)≥Ω+α(2−Ω).

Freeze the 56 stretched entries and leave all four own singletons free.
The new compact family contains r*_α and stays inside the original cube.
Its maximum satisfies Ω/2<Ω_b≤Ω, while its constant sure-profile floor is
at least Ω+γ, γ=α(2−Ω)>0. Hence it is at least Ω_b+γ. This proves the
existence reduction exactly as stated. The stretch need not increase η;
the proof only uses its uniform continuity to retain positivity.

The optional neighborhood remark is also sound in its stated strict sense:
a sufficiently small enlargement of the frozen block keeps every sure
regret above the ORIGINAL Ω, while any new restricted maximum remains at
most that Ω. Exact constancy of Γ is not asserted for that optional box.

## 3. Smoothing and optimization are performed in the right order

The new source is not obtained by stretching an already selected source
and retaining its old multipliers. At the NEW fixed-56-coordinate family,
the candidate first defines one common log-sum-exp F and one labelled tester
pool through L=2m+1, then minimizes F separately on each X_N, then maximizes
their window average over the four singleton parameters.

The actual complete quantile approximation is reward-uniform, so restricting
the reward domain does not change the error bound. Every inner minimizer
has full E within ρ_m+ε of the unrestricted η at its selected table. Every
selected table approaches Ω_b in value. After a subsequence, its limit r_∞
is a maximizer in this SAME family, not necessarily a worst table in the
original full cube.

For the outer envelope derivative, only the four singleton components of
each actual inner gradient are used. Finite separation gives a convex
combination of tuples whose projected gradient is normal to [-1,1]^4.
The SAME tuple combination defines the full vector G_m and retains all
the original source softmax weights. This is a proof certificate, not
correlated play or a convexification of equilibrium profiles.

The full entropy identity h_m−ε≤r_m·G_m≤h_m survives because it is an
identity for the original gain rows. The equality r_m·G_m=||G_m||₁ does
not follow on the restricted domain and is explicitly discarded. The
candidate uses no sign from the 56 frozen coordinates.

The common-pool chord estimates are unchanged: |g'|≤16, |g''|≤96, hence
F''≤H=96+256/τ. The source softmax weights control enlarged X_(N+1)
directions with error sqrt(2HΔ_N). All Δ_N use the SAME selected table
and SAME pool and telescope to at most 2+ε. Maximizing different tables
at different calendars, or dropping duplicate labels before differentiating,
would not establish this; neither is done.

## 4. Uniform margins and the new silent weights

The checked maximum-minimum singleton-margin declaration applies to any
positive unrestricted semantic minimum at r_∞. It does not require that
r_∞ maximize η on the full cube. Since all caps are at most one, it gives
s_(∞,i)≤1−Ω_b for all four players. Eventually all free singleton coordinates
are strictly below their upper face, so their projected normal components
are nonpositive. Their sum is exactly the OLD tuple's average actual
singleton-pressure observable.

The stronger uniform margin over EVERY inner minimizer is justified:
a violating sequence, reused at fixed r_∞, would have full E→Ω_b;
compactness of its semantic pairs would give a global minimum with
B_i−s_i≤Ω_b/2. This contradicts the checked margin. The argument uses
closed semantic compactness, not an actual limiting stopping law.

Shifting all finite atoms one step preserves prescribed coalition laws;
the new full cap is max(s_i,B_i)=B_i under that uniform margin. Whole
response-law rows shift from t to t+1, Never and the zero row stay fixed,
and one last finite label per owner is lost from the common pool. With
d_N=L−N+1 identical old late labels, its normalized lost mass is at most
1/d_N. The newly inserted initial rows have total unnormalized/old-partition
mass at most a_m=4exp(−σ/τ). This proves the partition comparison and the
scalar transport bound in (12), including actual singleton indicators.

After dropping the last two calendars, N+3≤L and the competitor domain
X_(N+3) has its complete after-support response N+3 still present. The
shifted profile uses dates 1,...,N and Never, precisely as Section 4 states.
The source recomputes λ̂ after the shift; it does not use the old λ as if
label multiplicities were unchanged.

The legal solo Quit0 direction, with all other prescribed clocks still
silent, gives the exact same-weight identity quoted before (14). Every
nonowner noninitial gain becomes zero. The new initial joining terms are
retained and cost at most 4a_m. Thus (14) controls every owner with the
SAME λ̂. No all-player-ties result or separately selected dual is needed.

The error accounting checks:

    ε=O(m^(−1/2)log m),       a_m=4exp(−σ√m),
    T_m=O((log m)/m)+O(a_m),
    B_m=O(m^(−1/4))+o(1).

Each Δ is counted at most three times, the removed calendar mass is
2/(m+1), and the further bad-error mass is at most sqrt(B_m). The pressure
observable is in [-1,1], so (15) follows after normalization; its denominator
is positive for sufficiently large m. Equation (14) with B_i−s_i≤2
then gives the advertised eventual θ_i≥Ω_b/4.

Finally the selected actual laws are reused at fixed r_∞ with their
transported λ̂ unchanged. The 2δ_m full-E, 4δ_m inactivity, and 16δ_m
simultaneous-derivative bounds are valid uniformly on the enlarged domain.
Singleton pressure and owner masses are law/weight quantities and remain
exactly unchanged. This proves the claimed co-realization of all fields.

## 5. Falsification checks and source audit

An independent exact-rational check generated 200 signed quarter-grid
tables, stretched all owner pairs simultaneously at rational α, and then
reselected all four own singletons independently. Across the eleven sure
coalitions it verified 1,975 positive instances of (6); the other 225 had
zero regret before and after stretching. This checks the algebra and its
zero-case boundary, not the existence of a positive worst table.

I inspected `minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
again at this review, and reread the original common-calendar source's
optimization and limiting-source proofs. The compact carrier and actual
quantile support/value declarations had already been inspected in my
[independent full audit of the silent bridge](CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE__BY_CODEX_TARSKI_PREMIUM.md).
That review's SHA is
`358aa33b10ca9c960ac4fc0b43811dcbf3ef0844d577136b0c034fea2095eb56`.
I independently rechecked the restricted-domain seams rather than treating
that earlier full-cube audit as automatic authorization to reuse a normal.

The precise new reduction is meaningful: the singleton-pressure program
may start from strict sure-regret separation instead of analyzing equality
at a nonsingleton sure-coalition minimum. It does not automatically bound
caps of other source modifications, supply a sign for mixed law changes,
or provide an arbitrary-table strategy producer. No unresolved mathematical
objection to the displayed source reduction remains.

## 6. Final-byte acceptance

PASS on the final mathematical packet
[Membership stretching and a singleton-fiber source reduction](../notes/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
SHA256
`1fdefe4acb70e12b789e045885bc8711cea707daa059a70daab197623afbaa70`.

I read the final packet through EOF and compared it with the independently
reviewed `7063965c...` source. The proof and source fields are unchanged.
The final definition-only revision correctly makes the gain the actual
unilateral payoff difference, uses owner-supported signed terminal-law
coefficients with no Never reward coordinate, keeps the zero tester as a
distinct label, and defines the derivative along independently sampled
simultaneous marginal chords. It does not substitute a public profile
mixture for that chord.

I also checked the added semantic reduction, common positive normalization,
boundary tests, fixed-data-before-accuracy quantifiers, exact declaration
correspondence, and six-part Lean handoff. In particular, the positive-gap
equivalence uses an actual response gaining more than η/2 rather than an
unproved cap-attaining response. Aggregation of late labels is restricted
to labels equal on the ENTIRE enlarged competitor domain, retaining their
derivatives as well as source values. The existence reduction may change
the counterexample table, and never transports an old full-cube normal to
the singleton fiber. No new Lean-check claim or strategy producer is added.

For these additions I inspected the named declarations in `SureExitSet.lean`,
`ExploitabilityGap.lean`, `TerminalExploitabilityRewardRobustness.lean`, and
`TerminalUniformPayoffSelection.lean` at their stated paths. I did not read
the parallel FRECHET review. No mathematical objection or requested edit
remains for these exact final bytes.
