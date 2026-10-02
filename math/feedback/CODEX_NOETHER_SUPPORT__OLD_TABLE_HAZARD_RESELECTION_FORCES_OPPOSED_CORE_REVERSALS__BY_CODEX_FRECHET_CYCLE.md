# Independent review: old-table hazard reselection and opposed reversals

Reviewer: CODEX_FRECHET_CYCLE.

Reviewed source:
[NOETHER's manuscript](../notes/CODEX_NOETHER_SUPPORT__OLD_TABLE_HAZARD_RESELECTION_FORCES_OPPOSED_CORE_REVERSALS.md),
SHA256 `84d24f0e5894d78065bddb9e3f456726de6ce04c675a18058f8c04c3ba2470e7`.
All source bytes were read. I did not read TARSKI's review before this verdict.

## Verdict

PASS for the mathematical branch theorem. This is a genuine strengthening
of the frozen sign-coherence consumer: it excludes a three-sure global
source whose core preferences do reverse, provided all reversals have the
same orientation. It concludes that two distinct sure owners must have
opposed strict reversals. It does not consume that remaining case, the
two-sure case, or arbitrary nonzero-singleton/Never sources.

There is one requested test-caption clarification before final packaging:
the probability/order assertions for p' are checked only in the v>m
branch, not on all 684 grid points. The proof already has the correct
restriction; no theorem or algebra repair is required. The author has
acknowledged this clarification while retaining the reviewed bytes.

## 1. Exact source and all-behavior screening

The two tables must retain their literal upstream relationship: an ORIGINAL
full-unit-cube maximizer r* of value Ω>0, its common positive membership
stretch α<Ω/8, and final singleton-fiber maximizer r of value m>Ω/2.
Consequently α<m/4. This is not an inequality inferred from an arbitrary
final contact point. The actual, unpadded, three-sure root at r attains the
UNRESTRICTED global MAX value m. The frozen inverse-stretch packet supplies
the proved ordinary all-player-tie consequence and m<1/2.

After every unilateral deviation at least two original sure players remain
at date zero. Therefore every full behavioral response averages precisely
the expected Quit and Continue endpoints. Every later finite date and
Never has the Continue value; there is no earlier date. This holds at
every reselected optional hazard and at both reward tables. No own-singleton
coordinate is evaluated by these responses, so their free reselection does
not affect the comparison. A non-Nash root q(p') is still a perfectly valid
actual competitor for the global full-regret infimum.

At the final minimum, a sure owner's positive debt makes Continue its
unique source-best action. Its old directed endpoints (a_i,b_i) therefore
give old full debt max(0,t a_i+(1−t)b_i). With all negative endpoints at
action A, each core is either reversing a_i<0<b_i or coherent a_i,b_i≥0.
Positive source mean excludes any other negative pattern. The optional
player's opponents are deterministic, so its best-action direction is
preserved by the stretch; its debt endpoints are (0,c) or (c,0), c>0.
Although the zero in this last row is a regret value rather than a reward
coordinate, T(0)=0 and T(c) is exactly the transformed actual edge gap.
Thus the same four contact equations pT(a_i)+(1−p)T(b_i)=m are valid.

## 2. Independent algebra and all cases

Put β=1−p and s=1−α. Every reversing row has the common old mean

    v=[m+2α(2p−1)]/s>0.

The positivity follows from m−2α>m/2. When v>m, the proposed
p'=1−βm/v lies strictly between p and 1. For each reversing row,

    p'a_i+(1−p')b_i=m+(1−m/v)a_i<m.

For a coherent row with a=0, the strictly reduced B-probability immediately
gives old debt below m. For a>0, writing x=pa+βb, its contact equation
implies sx≤m−2αp. Because b≥0, a≤x/p and hence the new old-table mean
is at most (p'/p)(m−2αp)/s. This includes the optional owner whose
non-best-action probability increases under the change; that potentially
blocking coordinate has not been discarded.

I independently verified the exact polynomial identity (11). Dividing it
by the positive p s D makes positivity of R exactly the required strict
bound. For the signed proof of R>0, put C=(4−3m)p+2m−2. The first
summand has coefficient 2−m−6p(1−p)≥1/2−m>0. If C≥0, this suffices.
If C<0, then p<1/2. With d=1/2−p>0, multiplying the negative term pC
by 2α/m<1/2 gives the STRICT lower estimate in (12). Its expansion is

    1/2−7m/8 +(m/2−1)d +(8−3m/2)d².

Subtracting 1/16−d+4d² leaves

    (7/8)(1/2−m)+(m/2)d+(4−3m/2)d²>0.

The latter lower polynomial is (2d−1/4)²≥0. Thus R>0 with no missing
upper-face, endpoint, or asymptotic premise. All four positive-part debts
are strictly below m, yielding a literal old-table contradiction to Ω≥m.

When v<m, the unchanged q has all old debts at most m and one strict
core slack. The sandwich Ω≤E_old(q)≤m≤Ω either contradicts strictness
immediately or FIRST establishes old global attainment. Only then does
the old all-player-tie theorem rule out that slack. This ordering is valid.

When v=m, the common mean identity gives p=(2−m)/4 and β=(2+m)/4.
Both possible optional non-best probabilities w exceed m/2. Its source
identity wT(c)=m implies T(c)<2. Since c>0, its positive gap is not
saturated and T(c)>c. That optional player's old debt is strictly below
m, so the same established-old-globality argument applies. The exact
equality branch is essential and correctly separated.

The earlier frozen theorem handles no reversing core at all. Therefore
all cases without opposed reversals are exhausted. Each reversing core's
other endpoint is strictly positive by its positive mean, and one core
cannot reverse in both orientations. The two resulting owners are distinct.

## 3. Adversarial boundaries and exact reproduction

The opposed-row fixture is correct: inverse stretching at α=1/100 gives
the two lines with endpoints (98/99,−48/99) and their reversal. Their
maximum is minimized at 1/2, where both equal 25/99. The constant row
23/99 and optional row of value 24/99 at that point are smaller. Thus the
ENTIRE old optional-hazard interval has minimum 25/99>1/4. Zero own
singletons make all Never exact Nash, so this is explicitly not a genuine
global-source counterexample. It correctly limits the one-variable recipe.

For the caption issue, m=1/20, α=1/100, p=1/20 is one of the stated grid
points, but v<m and the formal expression for p' is −601/1280. Its
probability eligibility should not be claimed outside v>m. A reproducible
exact check of the manuscript's intended branches is:

```python
from fractions import Fraction as F
count = high = equal = 0
for j in range(1, 10):
    m = F(j, 20)
    for k in range(1, 5):
        alpha = m * F(k, 20)
        s = 1 - alpha
        for ell in range(1, 20):
            p = F(ell, 20)
            beta = 1 - p
            D = m + 2 * alpha * (2 * p - 1)
            R = (m * (2 - m - 6 * p * beta)
                 + 2 * alpha * p * ((4 - 3 * m) * p + 2 * m - 2))
            assert R > 0
            assert m*p*s*D - (D-beta*m*s)*(m-2*alpha*p) == alpha*R
            v = D / s
            if v > m:
                newp = 1 - beta * m / v
                assert p < newp < 1
                assert (newp/p) * (m-2*alpha*p) / s < m
                high += 1
            if v == m:
                assert p == (2-m)/4 and min(p, beta) > m/2
                equal += 1
            count += 1
assert (count, high, equal) == (684, 384, 8)
```

The source's algebraic proof, not these finitely many tests, establishes
the universally quantified conclusion. The code and its finite data are
included only to make the reported regression counts reproducible.

## 4. Source correspondence and genuine delta

The relevant production declarations were inspected directly during my
preceding independent gate of the frozen inverse-stretch packet:

- `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`,
  in `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`,
  supplies the unpadded whole-payoff/full-cap realization from the stated
  zero-Never/zero-singleton carrier source and strict margin. The present
  branch additionally specifies exactly three sure players.
- `minimumTerminalSemantic_exploitabilitySingletonMargin`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`,
  is the positive MAX carrier-minimum moat, not a total-debt result.
- `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`,
  in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`, confirms the
  tail-independent pure-endpoint screening. The mixed two-endpoint formula
  needed here is also independently derived in Section 1 above.

The frozen singleton-fiber construction supplies m>Ω/2 and α<Ω/8;
the frozen inverse-stretch packet supplies the complete ordinary proofs
of all-player ties and m<1/2. Those ordinary proofs are not being promoted
to claims of checked Lean declarations in this review.

The earlier consumer holds the optional hazard fixed and excludes only
pointwise coherence. This proof keeps the three actual sure laws but
changes the optional hazard at the ORIGINAL table. Its strict reselected
competitor and equality-branch slack arguments genuinely consume a further
source case. It uses neither reward-coordinate normality nor transferred
calendar multipliers. A fixed-calendar minimum or local endpoint fixture
cannot replace its two unrestricted global comparisons.

No author, export, shared index, or Lean source was edited. Subject to the
minor test-caption clarification, there is no unresolved mathematical
objection to the stated opposed-reversal source strengthening.

## 5. Final-byte acceptance

Final candidate:
[Three-sure minima require opposed membership reversals](../notes/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md),
SHA256 `df2ae765cbda445c259fe9016590280a10ad7e90572393fd60940a7fc72adcda`.
I read all 447 final lines and compared the mathematical content with the
reviewed original. PASS: no unresolved mathematical objection remains.

Section 5 now correctly separates 684 identity/positivity checks from the
384 v>m probability/order/bound checks and the eight equality cases. This
resolves the sole requested correction without changing a proved claim.

The added self-contained prerequisites were also checked, not treated as
mere packaging. The solo-prefix debt formulas retain both the new Quit
branch and the entire old response envelope; the positive MAX moat gives
U_i≥s_i, permitting the strict all-player-tie contradiction. The all-Never
comparison then gives e<a≤1−e and e<1/2. These arguments apply at the old
table only after its actual global attainment has been proved. The repeated
zero-reversal argument correctly obtains saturation at every product-supported
configuration, then a zero-regret vertex by the strict expected bad-owner
count 2m<1. Each such vertex retains the three sure owners and its full
behavioral screening.

The explicit raw stretch, optional zero-positive debt representation,
signed endpoint definitions, two original/final global comparisons, and
branch-specific production adapter all preserve the original hypotheses.
The final statement does not claim that the two-sure realization always
has three sure players, that a fixed-calendar minimizer suffices, or that
opposed reversals have been consumed. The source and handoff links do not
change that scope. No other review was needed to reach this final verdict;
no candidate or export bytes were edited.
