# Independent check of the positive-Never earlier-cap dispatch

Reviewer: CODEX_NOETHER. Ordinary mathematical review, not a Lean check or
an export seal. No parallel proof or counterpart review was read.

Reviewed mathematical surface: “Positive-Never global minima have an earlier
finite cap maximizer” through EOF of
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, extracted section SHA256
`50e7bb588e75ed41dd1868119aeeb0964d198266afd188c282e59abdb55b01ac`.
The exact extracted hash was checked directly.

## Claim and verdict

Fix any finite nonempty player set and bounded quitting rewards, with Never
payoff0, nonnegative own singleton levels s_i and Σ_i s_i>0. Let D_* be the
infimum of SUM unrestricted terminal deviation debts over actual independent
finite stopping laws. Take the produced marked-calendar representation of
an actual minimizing sequence: T compact, c=max T empty of prescribed mass,
all complete caps attained, and every prescribed payoff and complete cap the
limit of its original-game counterpart. If every represented law has positive
Never mass, some player's cap is attained at a finite t∈T strictly before c.

PASS for this actual-source branch exclusion. The conditional head/tail
reweighting has complete-cap finite transport, its local debt polynomial is
genuinely multi-affine, and its all-tail values force the contradiction stated.
I found no mathematical repair. The proof does not require D_*>0, does not
prove debt zero or UE, and does not identify the represented calendar with
an executable discrete-clock strategy. Those scope restrictions are correct.

## Load-bearing implications checked

1. Under the negation of the conclusion, attained caps really are the finite
   late values L_i=W_i+s_i∏_{j≠i}α_j. The nonnegative own levels ensure that
   this late response dominates Never. Every other finite response is strictly
   below L_i. The cases c=0 and a calendar containing only the empty final
   point reduce to all Never, rather than supplying an interior variation.

2. For a fixed mixture-continuity cut K<c, tail masses S_i≥α_i are positive.
   Every varying player has both H_i>0 and S_i>0, so its original coordinate
   x_i=S_i is strictly interior. Coordinates with H_i=0 must be fixed at1,
   as the manuscript does; they need no fictitious conditional head.

3. Equation(HT5) is exact for every future finite tester and Never. Whenever
   some opponent selects its head, an opponent quits at or before K and the
   observer's later clock cannot affect the first coalition. On the remaining
   event all opponents use their unchanged conditional tails, with probability
   X_{−i}. Thus the late-minus-tester deficit is exactly X_{−i} times the
   conditional-tail deficit. Its original coefficient is strictly positive,
   including when i itself has zero head mass. This proves domination for
   ALL future testers throughout the parameter cube, not only any finite
   selection of near-final tests. Signed passive or joint rewards do not
   change the identity.

4. The earlier tests form the compact set T∩[0,K]. Their continuous strict
   gaps have a positive minimum, when that set is nonempty. The uniform
   bounded-reward coupling bound controls every pure tester simultaneously
   as x changes. Therefore the asserted complete-cap identity holds on an
   actual neighborhood of the original interior point. Its polynomial is
   Σ_i L_i−Σ_i U_i, not an arbitrary surrogate: each prescribed payoff is
   separately affine in every independent mixture coordinate, and L_i is
   the literal pure-c response.

5. The finite transport does not follow merely from the older finite-atomic
   mixture domain. It is correctly supplied separately. At a zero-mixture-mass
   location K, the original collapse maps converge almost everywhere, and
   the indicator of the selected original head converges in L¹. A retained
   positive atom lies wholly on one side; its quantile interval is never
   split. For each varying player, H_iⁿ and S_iⁿ stay bounded away from0,
   so the reweighting factors are uniformly bounded and converge in L¹.
   Multiplying the old weak-* density by those factors gives the claimed
   new weak-* density. The product convergence follows by rectangle tests
   and L¹ density, with a fixed uniform product bound.

6. The semantic kernels and the entire old tester sets remain unchanged.
   Their moving-kernel L¹ convergence therefore continues to apply against
   the new bounded densities. It retains ties at positive atoms, every empty
   tester, the final finite c tester, and Never separately. Convergent moving
   maximizers prove the upper cap bound; fixed limiting tests prove the lower
   bound. Consequently EACH fixed x has actual finite approximants and debt
   at least D_*. There is no division of approximation error by a shrinking
   tail mass, and no simultaneous approximation for all x is needed.

7. An interior local minimum of a multi-affine polynomial is constant. In
   its Taylor expansion about the interior point, every nonconstant monomial
   is square-free. The lowest nonzero homogeneous part has zero average on
   a symmetric sign cube and is nonzero somewhere on that cube, by independence
   of its Walsh monomials. It has both signs; along a sufficiently small
   negative direction the higher-order terms cannot prevent decrease. This
   also covers a zero-dimensional parameter cube trivially.

8. Constancy gives F_K(1)=D_*, NOT D_T(v)=D_*. This distinction is essential:
   an earlier cap may overtake the extrapolated late polynomial at the
   all-tail vertex. The proof uses only the polynomial equality. Taking
   continuity cuts K↑c, empty c and α_i>0 imply that every conditional tail
   converges in total variation to Never. Hence U_i(v),W_i(v)→0 and L_i(v)→s_i,
   which forces D_*=Σ_i s_i without any assertion about actual vertex debt.

## Exact original-game source and nearby overlap

I inspected `exists_exactRoot_terminalExploitability_le_and_debtSum_descent`
in `UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean`, its
debt-sum descent proof, and its quantitative dependency
`quittingTerminalDeviationDebt_rootThenContinuation_le_sub_min` in
`UniformEquilibrium/Quitting/Boundary/Repair/TerminalDebtSingletonDescent.lean`.
At actual all Never choose j with s_j>0, reward bound M>0 and gap=s_j.
Its actual continuation payoff is0 and its complete debt is s_j. The supplied
decrease is min(s_j²/(8M),s_j/2)>0. The theorem internally produces an exact
finite-game Nash root; prepending it to all Never is a one-date/Never finite
profile. Thus D_*<Σ_i s_i follows with the exact hypotheses of the declaration,
without a supplied root, an auxiliary continuation value, or a compact-profile
application of the Lean theorem.

The marked weak-* representation and complete moving-tester convergence are
the ordinary mathematics of Section35 of
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, whose exact original body
I independently checked previously. This review uses that produced source,
not an assumed minimum on arbitrary compact calendars. The new reweighting
transport is independently checked above.

For nearby implemented restrictions I inspected
`minimumTerminalSemantic_singletonMargin` and
`minimumTerminalSemantic_is_allContinuePlateau` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
Those are quantitative cap/singleton and auxiliary-root statements on the
actual semantic carrier. They do not localize an attained cap to a finite
time before c. The existing prefix descent supplies the strict all-Never
comparison here; it does not by itself consume the near-final continuum of
binding tests. The project's multi-affine potential exclusions concern
different supplied source/root potentials, not this local complete-debt
polynomial or its fixed-cut transport. No whole-game coverage claim is made
from these bounded comparisons.

## Remaining scope

This excludes the all-positive-Never, late-only-cap branch of a produced
actual minimum for any finite cardinality. Other coalition rewards may be
arbitrarily signed. It neither removes an earlier binding response nor makes
it shared, atomic, or strategically harmless. Zero Never mass breaks the
conditional-tail-to-Never step. With Σ_i s_i=0, all Never already has debt0,
and the strict comparison is unavailable. In a Fin4 no-UE application one
must normalize the raw table first and select a NEW minimizing sequence;
the proof does not transfer an old minimizing law through normalization.

The next actual-source question is consumption of an earlier finite binding
cap together with the still-present late constraints. This verdict is bound
only to the extracted section hash above; it is not an export or UE seal.
