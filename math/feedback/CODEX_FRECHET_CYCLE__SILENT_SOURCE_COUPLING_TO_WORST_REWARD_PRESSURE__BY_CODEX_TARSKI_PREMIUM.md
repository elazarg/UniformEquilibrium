# Independent review: silent source, all-owner weights, and worst-table pressure

Reviewer: CODEX_TARSKI_PREMIUM.

Reviewed source:
[CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE.md](../notes/CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE.md).
Exact reviewed SHA256:
`0e60914311f2ce46855e87a518400543607d0e2f233bce97f9fd70993b6754db`.

## Verdict and scope

PASS on the stated ordinary-mathematics source bridge. I independently
reconstructed the law transport, partition accounting, enlarged derivative
estimate, all-owner screen, and averaged scalar extraction, then checked
the exact candidate through EOF. No mathematical repair is requested.

This genuinely co-realizes the claimed fields on one actual sequence with
one NEW tester law at each source. It neither identifies that law with the
old softmax law nor declares an individual source reward gradient normal.
It supplies no sign for a two-law mixed coefficient, full-regret descent,
or equilibrium producer. This is not a Lean seal or a claim that Ω>0.

The input is NOETHER's coupled source at SHA
`fade3cb825778caf0c76a1a4d6b9820e43bd6f430abf6f8af64b5c95973dd854`.
I read that input and its independent source audit. I also inspected the
named quantile and compact-semantic declarations listed below. The present
review is of the new bridge, not a replacement for the input's own review.

## 1. Uniform margin and actual silent laws

The source estimates are uniform over EVERY minimizer of every smooth
f_N in the selected window, not just the finite tuple later chosen by
outer separation. This is essential for the margin argument and is
available from the input's pointwise bounds on f_N and F.

Suppose the claimed margin Ω/2 failed along arbitrarily late windows.
Choose violating actual minimizers and stabilize one owner. Reuse their
literal laws at the fixed worst table r*. The payoff and cap reward
Lipschitz estimates imply that their semantic pairs are near-minimizing
there and that their violating margins have limiting upper bound Ω/2.
Compactness gives a carrier minimum; the checked MAX singleton-margin
theorem gives its margin at least Ω. This is a contradiction. No minimum
point is assumed to be an actual strategy.

Shifting all finite clocks by one and keeping Never unchanged preserves
the terminal coalition law exactly. All positive-date response laws are
shifted old response laws; Never's response law is unchanged. The only
new response is immediate Quit, with value s_i. Thus the shifted full cap
is max{s_i,B_i}=B_i under that uniform margin. This verifies the actual
source provenance, not merely equality of a prescribed payoff vector.

## 2. Partition and whole reward-row transport

For each owner the new labels 1,…,L correspond to the old labels
0,…,L−1. The old label L is removed, the initial label is added, and
Never and the separate zero row remain. This bijection preserves the
whole first-quitter outcome distribution, not just its value at r_m.

For an old source in X_N, all labels N,…,L are identical, so their
multiplicity is d_N=L−N+1. The lost total probability is therefore at
most 1/d_N. The initial gain satisfies

    s_i−U_i=d_i−κ_i≤E−σ.

Since the old partition contains a maximum-gain term, the added numerator
divided by the old partition is at most 4 exp(−σ/τ). Therefore

    Zhat/Z=1−ell_N+a_N,
    F(phat)≤f_N+τ a_m

are exact or correctly directed as stated. The exponentially small error
is indeed needed: a generic τ log|J| error would not be harmless after
multiplication by the Hessian scale 1/τ.

For a scalar observable in [−1,1], subtracting the old normalized mean
from the new one gives numerator magnitude at most 2(ell_N+a_N), divided
by 1−ell_N+a_N. With d_N≥2 this is at most
4(1/d_N+a_m). The analogous vector estimate is twice as large because
the reward rows have ℓ¹ norm at most two.

The actual singleton coefficient is an admissible scalar observable:
P_deviation({i})−P_prescribed({i}) lies in [−1,1] and transports with the
whole response law. The new initial coefficient is computed from the
actual singleton-{i} outcome, since every opponent Continues initially.
This checks the delicate probability-vector seam in the proof.

## 3. Menu indexing and new-weight directional control

Removing calendars 2m−1 and 2m leaves N≤2m−2. Hence the shifted source
lies in X_(N+1), every tested endpoint lies in X_(N+3), and
N+3≤2m+1=L. The common pool includes the COMPLETE tester N+3.
Tests N+2 and N+3 cannot be merged on X_(N+3); the candidate does not
merge them. Only labels at or beyond N+3 coincide on that whole domain.

The source need not minimize F on its shifted calendar. For a simultaneous
chord to any allowed endpoint, the fixed-gain derivative bound is sixteen
and the second-derivative bound is ninety-six. The softmax Hessian adds
at most 256/τ, so the input's H bound still holds at every point of the
chord. A negative derivative −c gives the actual feasible step c/H≤1.
Comparing its value with the global f_(N+3) floor yields exactly

    Rhat_N²=2H[Δ_N+Δ_(N+1)+Δ_(N+2)+τ a_m].

The derivatives here use the newly recomputed softmax weights at phat.
No replacement multiplier from an unrelated minimax problem enters.
The common-pool entropy identity independently supplies inactivity at
most ε for these same weights.

## 4. Same-weight all-owner screening

I checked the solo endpoint directly. If k Quits initially, all nonowner
noninitial response gains become zero. A nonowner's initial response
instead has changed gain r_i({i,k})−r_i({k}); this term cannot be omitted.
All k-owned gain increments equal U_k−s_k. The labelled zero row has
zero increment and introduces no extra term.

Writing the exact weighted derivative as in the candidate gives an upper
bound theta_k κ_k−Ghat plus the initial joining contribution. The latter
is at most two times the new initial mass, hence at most 4a_m. Combining
the derivative LOWER bound and Ghat≥E−ε proves

    theta_k κ_k≥E−ε−Rhat_N−4a_m.

Since κ_k≤2, the asserted eventual theta_k≥Ω/4 follows. The owner-debt
near-tie bound also follows from the same inactivity identity. The
all-owner conclusion is thus genuinely attached to the pressure weights,
not imported from the earlier, separately selected silent certificate.

## 5. Averaging, fixed-table transport, and exact rates

There are m+1 old calendars and exactly two are removed, so the lost
tuple mass is q_m=2/(m+1). Every three-step gap is a sum of three old
adjacent gaps; each adjacent gap appears at most three times. With the
original tuple weights, Cauchy–Schwarz gives the claimed B_m bound.
It is safe to omit the remaining total-mass factor because it is at most
one, not to silently renormalize the tuple distribution.

The reciprocal sum is over d_N=4,…,m+2, so T_m tends to zero. More
explicitly, its nonexponential part is O(log m/m). Since τ=m^(−1/2),
H=O(sqrt m), and a_m is exponentially small in sqrt m, one has

    B_m=O(m^(−1/4)) plus an exponentially small term,
    gamma_m=sqrt(B_m)→0.

Only convergence, not these particular displayed orders, is needed.
For finite m, B_m is strictly positive, so the Markov step dividing by
gamma_m is legitimate. For sufficiently large m the remaining good mass
1−q_m−gamma_m is positive. Removing bad entries costs at most their
mass because the pressure is bounded below by −1. The stated scalar
extraction follows with its actual denominator.

The unnormalized new-gradient average differs from the old normal by at
most 2q_m+2T_m in ℓ¹. The factors are correct: dropped rows cost at most
two per unit mass, and vector transport costs twice scalar transport.
It has the same limiting normal but need not itself be a finite-stage
normal; no such claim is made.

Finally the weights are RETAINED when the selected laws are reused at r*.
A reward perturbation δ changes full E by at most 2δ, weighted inactivity
by at most 4δ, and every simultaneous four-law directional derivative by
at most 16δ. The last estimate sums four one-coordinate increments, each
at most 4δ. It is uniform over the entire allowed endpoint domain.
Singleton pressure and owner masses are unchanged because they are
law/weight quantities. All claimed fixed-table errors therefore vanish.

## 6. Falsification checks and declaration correspondence

I ran a separate exact arithmetic test on eighteen signed rational source
and window-boundary cases, including the smallest late-label multiplicity
d_N=2 before endpoint-calendar removal. Full prescribed and shifted
response coalition laws agreed exactly. Eighty-digit arithmetic verified
the partition identity, lost-mass bound, pressure transport bound, and all
seventy-two solo-screening identities. Initial and Never responses were
included. These are algebra checks, not examples of positive Ω or sampled
global minimizers.

The important potential failures were explicitly tested in the proof:
loss of a late row, an added unpriced joining row, a payoff-only rather
than law-vector transport, an endpoint outside the common tester pool,
a nonuniform chosen-minimizer margin, a generic entropy loss at the
wrong Hessian scale, renormalizing the wrong averaged weights, and
recomputing softmax after fixed-table transport. None occurs here.

Named declarations inspected:

- `quittingTerminalSemanticCarrier` and
  `quittingTerminalSemanticCarrier_isCompact` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`;
- `exists_finiteClockSemanticPair_exploitability_eq_upper`,
  `quantileClockSupport_fin4`, `quantileClockRadius_fin4`, and
  `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.

The quantile declarations justify the input's uniform finite-calendar
near-minimality without assuming a common actual strategy limit. This
review adds no Lean trust claim to the ordinary-mathematics bridge.
The source hash was rechecked after the audit and remains unchanged.
