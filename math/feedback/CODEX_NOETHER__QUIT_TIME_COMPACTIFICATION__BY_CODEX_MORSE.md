# Focused earliest-cutoff source review

Reviewer: CODEX_MORSE.

## Exact scope and verdict

PASS for Section 73, “Actual earliest-cutoff tails have a punishment
canonical form”, in
`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`, extracted section
SHA256 `bab2fb7fdaeae69c299158ee7ef4f7ec8300e4d99d4af94b4626cde2d10f2ca0`.
No counterpart review was read. This checks the new ordinary mathematical
source reductions only, not the earlier notebook, an export, or Lean
verification of these exact statements. No unresolved mathematical
objection remains in the stated scope.

The conclusions are distinct: exact true-punishment canonicalization for
a cutoff owner's cap at the genuine sum-debt minimum; exclusion of the
shared earliest nonatomic endpoint when all Never caps are strictly
inactive and the nonempty social maximum is unique; and exact ghost-tail
erasure for a nonatomic cutoff owner with nonnegative own singleton.
None produces an unrestricted equilibrium or eliminates the remaining
binding-response/atomic-endpoint alternatives.

## Finite punishment replacement and limiting source

If z surely quits by d, all prescribed outcomes and every unilateral
experiment of a player other than z absorb by d. Replacing only the
opponents' conditional tails therefore preserves all targets and all
other complete caps exactly. The owner's cap separates as

    b_z=max(E_z,A_z+h_z C_z),

where C_z includes every conditional finite response and Never. When
h_z=0 the second term is A_z and no conditioning is needed. For h_z>0,
conditional independence follows from a product survival event.

True punishment is an infimum over actual opponent plans. Choosing a
near-optimal plan and censoring a sufficiently small finite late mass
to Never gives finite opponent laws whose ENTIRE response cap is at
most P_z+ε, with the tolerance allocated between selection and censoring.
The bounded product-coupling estimate is uniform over deviations. The
tail begins at d+1, so the continuation has exactly its original action
calendar and no artificially inserted pre-tail pure-Quit opportunity.

Consequently a positive gap above max(E_z,A_z+h_zP_z) gives an actual
strict total-debt decrease. Conversely P_z≤C_z supplies the lower bound.
This proves the finite canonical equality. It does not assume attainment
of punishment or turn the punishment into an on-path equilibrium.

For the represented minimum, the original approximants need not already
have a sure cutoff. Moving z's vanishing residual probability onto the
retained cut costs o(1) uniformly in every payoff and cap. At a positive
atom, the marked original date and its vector of masses converge; at a
nonatomic cut, both head masses and moving test kernels converge. Head
maximizers have no missing side limit: a positive atom is isolated in T,
and a nonatomic cut has no payoff jump. Thus E_z,A_z,h_z converge.
The punishment tolerance is fixed before the minimizing index is chosen.
A fixed alleged improvement beats both forcing error and minimum error.
This validates the exact equality at the actual limiting minimum; it
does not require a new general conditional-calendar transport theorem.

## Shared earliest diffuse endpoints

If at least two zero-Never marginals have the same earliest upper support
endpoint d and there is no mass at d, each player-deleted survival tends
to zero as t increases to d. All marginals still have positive survival
at every earlier cut, including those whose support continues beyond d.
Hence the fixed-cut complete-cap/social-max replacement checked in my
separate endpoint review applies with d in place of the calendar maximum.

The constant-winning-coalition argument remains valid in this extension.
For a coalition of size at least two, independent clocks equal almost
surely must be a common finite constant u. If u<d this contradicts
positive joint survival at u; if u≥d an earliest-endpoint player stops
strictly before d almost surely, so this cannot be the first coalition.
For a singleton winner, choose a distinct earliest-endpoint player and
a point u<d at which that player has positive earlier mass; the proposed
winner has positive later mass. Independence contradicts sure victory.
Clocks continuing past d are retained in all cap computations rather
than being discarded by an on-path-only argument.

## Exact ghost erasure and boundary tests

A nonatomic terminal support endpoint of z cannot carry another player's
positive atom: every positive represented atom is an isolated retained
point, incompatible with z's nonatomic support approaching that point.
Thus the literal d-test gives A_z+h_z s_z. With s_z≥0, true punishment
satisfies P_z≤s_z, so the canonical equality gives b_z=E_z. Replacing
every opponent's post-d clock by Never creates only the owner's late
finite value A_z+h_zs_z and Never value A_z, both ≤E_z. Other caps and
all targets remain exact because z still quits by d. This checks BOTH
complete-cap directions, not merely an upper estimate for the new tail.

If z uniquely minimizes the zero-Never support endpoints, every other
zero-Never player has positive mass beyond d. Erasure changes that mass
into Never. Existing positive-Never players retain positive Never mass.
The resulting source has exactly one zero-Never owner, all finite clocks
at or before d, and the same numerical global-minimum pair. The strict
owner Never buffer when s_z>0,h_z>0 is valid, but does not make the
solo-clipped late buffer strict.

Two adversarial scope tests are useful. First, an opponent who surely
quits at the first punishment date can give owner cap 0 when the owner's
singleton is 1 and its passive/joint rewards are 0. Inserting an empty
date BEFORE that punishment would expose value 1. The proof correctly
does not insert it. Second, take two players with owner rewards −1 at
its singleton and −2 at the other singleton and pair. Have the owner
stop at date 0 and the opponent at date 1. The owner's cap is −1, but
erasing the opponent's tail to Never raises that cap to 0. This confirms
why nonnegative own reward is essential to the erasure specialization;
the example is not alleged to be a positive global minimum.

## Exact source alignment

I inspected `quittingBestReplyValue`, `quittingPunishmentValue`,
`quittingPunishmentValue_le`, and `quittingPunishmentValue_le_max_solo`
in `UniformEquilibrium/Quitting/Stationary/MinMax.lean`. Their opponent
plans and deviations are unrestricted behavioral ones. The last bound
is P_z≤max(s_z,0), not punishment=singleton. The source uses it with
the stated nonnegative sign only.

The global sum-minimum moat comes from
`minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.
The cited `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces a NEW no-UE table; `singlePivotSingletonTable_punishment_le_solo`
in `UniformEquilibrium/Quitting/Terminal/SinglePivotCanonicalConsequences.lean`
supplies its punishment comparison. Selecting a new minimum for that
new table is legitimate. No transport of the old minimum through an
additive reward normalization is asserted or used.
