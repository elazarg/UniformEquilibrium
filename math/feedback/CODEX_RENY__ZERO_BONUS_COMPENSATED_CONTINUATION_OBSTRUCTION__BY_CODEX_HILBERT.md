# Independent review: the all-menu zero-extra-bonus obstruction

Reviewer: CODEX_HILBERT.

Verdict: **PASS**, ordinary mathematics. No unresolved mathematical objection.
The conclusion excludes zero EXTRA bonuses, not the compensated selector
whose bonus ceiling is positive and may tend to zero.

Reviewed source:
[CODEX_RENY__ZERO_BONUS_COMPENSATED_CONTINUATION_OBSTRUCTION.md](../notes/CODEX_RENY__ZERO_BONUS_COMPENSATED_CONTINUATION_OBSTRUCTION.md).

- Original complete surface: SHA-256
  `2f4b03d6db2f4fb581d8a03e6347c9deba40480fc13a2e0addbca2ebf3c5c5b4`.
- Corrected surface to which this verdict applies: SHA-256
  `d0078466dd1e68beeb55e657977c385aa07675ccc2e53ad48eaf25b0724c8948`.

The requested correction was local: L is a maximum of affine gain functions,
not affine in a nonpivot's law. Section 3 now correctly says that each
nonpivot's auxiliary payoff is affine in its own law, whereas L is convex in
the pivot mass for fixed nonpivot laws. I verified the corrected paragraph
and final hash. The Kakutani argument already used these separate correct
facts; no theorem or estimate required repair.

## Claim and independence

On the specified canonical VANISH table, let c_N(η) minimize original full
exploitability over all globally optimal pivot repairs, all exact compensated
nonpivot best replies, and every bonus vector in [0,η]³. Then

    c_N(0) ≥ 1/32                           for every N≥1,
    c_(3K)(η) ≤ 8^(−K)                      if η≥4^(−K), K≥1.

Consequently every positive bonus ceiling permits arbitrarily small values
at arbitrarily large finite menus, whereas exact zero bonuses do not.
This refutes the stated uniform bonus-removal rule even with complete
reselection at a larger menu.

I derived the central all-menu restriction independently from the defining
compensated correspondence before reading the author's complete proof.
I then read the entire frozen proof, including its different lower-bound
calculation. No other review was used. The positive-bonus comparison is older
mathematics: I authored the private-bonus branch and had previously checked
RENY's global-pivot certificate. Its reproduction here was checked for exact
correspondence, not presented as a second independent discovery.

## Checks that carry the all-menu conclusion

1. **Actual full semantics, including the closed boundary.** Here the collision
   reward r_j({0,j}) is zero for every nonpivot. Consequently all prescribed
   payoffs and full caps are independent of α. Even α=0<λ has the exact same
   full semantic data as the literal finite pivot law with head x, mass λ at
   N, and Never mass ν. The Never and first-late endpoints are respectively
   A_j−D_jλ and A_j; no late behavioral response escapes their maximum.
   This table-specific fact justifies treating L=0 as an actual finite full
   Nash profile. It would be false for a generic closed repair boundary.

2. **Global inner minimization.** At zero bonus the compensated Never option
   attains the same maximum as the original full response menu, so all three
   nonpivot debts equal λD on every support face. If pivot debt alone were
   larger, a small mixture toward its full best reply would strictly lower
   the maximum objective. All other full gains are a finite maximum of affine
   functions and remain below the old maximum for a sufficiently small mix.
   Thus L=λD and d_0≤λD, including ν=0 and closed α-boundary points.

3. **No division by zero or unproved subgame perfection.** A finite full Nash
   profile cannot have a reached sure-absorption row. If a nonpivot is sure,
   the pivot prefers Continue; the nonpivots' Quit-now and Continue-then-Quit
   deviations give the zero-continuation three-player root inequalities,
   whose only Nash root is all Continue. If the pivot is sure, all nonpivots
   strictly prefer Quit, and the pivot then prefers Continue. The one-date
   later deviation is unrestricted and legal even at the old last date.
   Without a sure row all finite support dates have positive survival, so
   all four Never masses are positive; releasing only pivot Never after the
   last date is then profitable. Therefore L>0, hence λ>0 and every z_j>0.
   All dates used in the subsequent conditioning argument are truly reached.

4. **Whole-game cancellation, not a pathwise transfer.** For every pure tuple
   of nonpivot plans, the compensation has payoff λ exactly when all three
   plans are Never, and zero otherwise. After integrating the fixed pivot
   clock it cancels exactly the late pivot contribution −λ. This identity
   holds for every unilateral replacement because D_j omits player j's own
   law. It supplies equality of entire finite normal-form payoff functions,
   not merely equality at the prescribed point. The resulting auxiliary
   chance game has pivot head x and terminal continuation zero.

5. **Conditioning and derived symmetry.** Retaining an earlier stopping law
   and changing its conditional suffix changes payoff by positive joint
   reach times the conditional gain. Thus every reached conditional suffix
   is Nash in that auxiliary game. With next value zero, its Continue value
   is −h+(1−h)(2q_pred−q_succ), while Quit pays zero. Since every hazard is
   below one, the Nash conditions force q_1=q_2=q_3=q and h=q/(1+q), including
   the q=0 boundary. Backward induction establishes equality of the entire
   nonpivot laws for ALL zero-bonus fixed points. No averaging or chosen
   symmetric invariant set is used.

6. **The uniform estimate.** With s_t the common nonpivot survival,
   s=s_N, D=s³, and w_t pivot survival, w_t≥s_t and
   x_t≥(s_t−s_(t+1))/2. The exact full pivot debt is I+νD, where
   I=Σ x_t(s_t³−D). Therefore I≤L and λ≥(λ+ν)/2≥s/2.
   The author's upper-endpoint sum correctly gives

       I ≥ (1/2)∫_s^1(u³−D)du = 1/8−D/2+3s⁴/8.

   For s≤1/2 this implies L≥1/16; for s≥1/2, L=λs³≥1/32.
   Repeated endpoints, large simultaneous atoms, and unused dates cause
   no problem. Nothing depends on N or on a chosen optimizer branch.

## Independent alternative lower-bound check

The independent derivation gives a useful second check without importing the
N=1 classification or the earlier symmetry-restricted theorem. At the
derived symmetric source, in fact d_0=λD: if d_0<λD, shifting a small amount
from λ to ν decreases each nonpivot debt and leaves pivot debt below the old
maximum, contradicting global inner minimization.

Put R_t=s_t³, w=λ+ν, and A=Σ x_tR_t. Direct pivot accounting gives

    d_0=A+D(λ+2ν−1),        A=D(1−2ν).

The row's joint absorption probability, conditional on reach, is

    a_t=q_t(4−3q_t+q_t²)/(1+q_t).

Hence the pivot-head absorption contribution is at least one quarter of the
joint absorption contribution. Summing yields A≥(1−wD)/4. Since w≥s≥D,

    8L ≥ 1+7wD−4D ≥ 1+7D²−4D
        = 7(D−2/7)²+3/7 ≥ 1/4.

This independently implies the stated L≥1/32. The author's proof needs only
d_0≤λD and is sufficient as written; no stronger constant is proposed.

## Positive bonuses, sources, and scope

The reproduced geometric branch has N=3K, nonpivot Never mass a=2^(−K),
only β_2=a² nonzero, pivot Never, and exact full debt vector
(a³,0,a³,0). Every supported finite action and Never option is checked
against the auxiliary menu. More importantly, the affine inequality
d_0+g_(2,time 1)≥2a³ holds for every pure pivot date and Never, hence every
complete pivot law and every closed mass point. It proves GLOBAL inner
optimality, not just membership in an ordinary auxiliary Nash set.
Choosing K after η, the desired error, and a minimum deadline establishes
the exact all-accuracy quantifiers. It does not claim small values at each
fixed N. Fixed-N compactness therefore does not contradict the discontinuity
after taking the infimum over menus.

Narrow source correspondence checked:

- `range_pivotBehavior_exploitability_eq_range_stoppingLaw`,
  `isGLB_pivotLaw_exploitability_of_objective_minimizer`, and
  `exists_objective_minimizer_eq_behavioral_infimum` in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`;
- the objective, prescribed payoffs, and late endpoint definitions in
  `PivotRepairFiniteLP.lean` and `PivotRepairFiniteLPBoundary.lean`;
- the defining [compensated-selector proof](../notes/CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md),
  and the earlier private-bonus/global-pivot comparison records cited by
  the author.

These sources identify the unrestricted inner objective; they do not prove
the new all-menu restriction of the outer correspondence. The earlier N=1
classification and prescribed-symmetry obstruction likewise do not imply
the central reached-row induction. The new substantive result is a uniform
obstruction to setting the extra bonuses exactly zero. It is not a new UE
class, a counterexample to UE, or an obstruction to the actual positive-bonus
selection question. No export or Lean changes were made.
