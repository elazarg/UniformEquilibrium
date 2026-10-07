# Independent review: the unique diffuse earliest owner

Reviewer: CODEX_BROUWER. Ordinary mathematical review, not a Lean build or
export seal. No counterpart review was read.

## Exact surface and verdict

The reviewed section is “Fixed-cut reachability and the unique diffuse
earliest owner” in
[CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
starting at that heading and stopping before Section73. Its extracted SHA256
is `d904c6f1a3b8d9f0a1b746d5f7436243c2612827cc71863188fbb88c3d707509`.
I also read the necessary Section73 punishment and ghost-tail arguments and
the complete small-prefix erasure proof in MORSE's Section36, not their
counterpart feedback.

**PASS for the stated source exclusion.** No unresolved mathematical
objection. This consumes a genuinely attained positive GLOBAL sum-debt
minimum. It is not a theorem about every positive-debt profile, every
conditional tail, or every independently supplied compact-calendar law.

For any finite nonempty player set with original Never payoff0 and bounded
signed rewards, the excluded configuration is: one unique earliest
zero-Never owner z, s_z≥0, and no finite marginal atoms at or before its
support endpoint d. Other reward rows may be signed, clocks after d may
have atoms, and any number of Never responses may bind. The conclusion
does not exclude shared earliest zero-Never owners or earlier finite atoms.

## Fixed-cut regeneration

The finite iteration is correctly quantified. Fix an available nonatomic
cut b FIRST, with every S_i(b)>0. Each intermediate survival product is
bounded below by the same R(b)>0. A full-charge removal of total conditional
head mass κ=δ/(4M) multiplies that product by at most exp(−κ). Hence fewer
than N full-charge steps are possible once exp(−Nκ)<R(b). The last removal
has mass at most κ and reaches b exactly.

Atomlessness through b supplies the intermediate cuts. If a real level cut
lies in a gap of the compact test set, a gap endpoint has the same cumulative
mass. Since the target mass lies strictly between0 and the mass before b,
this endpoint is an actual test strictly between the current cut and b.
No unavailable between-date test is introduced.

The argument neither assumes nor needs a uniform lower bound on R(b) as
b approaches the endpoint. The number of iterations may diverge with b.
Repeated conditioning is conditioning the ORIGINAL laws once at the final
cut; for each fixed b its normalizers remain bounded by 1/S_i(b).
Consequently the original realizing sequence and the old moving response
kernels give the required actual finite profiles and complete-cap limits.
This avoids both an infinite-update realization claim and a division of
an approximation error by a vanishing survival probability.

The underlying small-prefix theorem is being used literally: a cap moat
excludes all early responses locally, the fixed conditional laws give a
multi-affine polynomial, and the closed-and-open continuation argument
preserves the complete minimum until the prefix is erased. Polynomial
constancy alone would not identify the entire path as actual minima; the
proof retains the extra cap argument.

## Ghost-tail surgery and the final contradiction

At endpoint d the prescribed owner z quits surely by d. Every unilateral
replacement of another player still has z's original law, so all such
profiles absorb by d. Changing only opponent clocks strictly after d
therefore preserves ALL targets and every nonowner cap exactly.

For z the correct old decomposition is

    b_z=max(E_z,A_z+h_z C_z),

with E_z the maximum of its actual tests≤d and C_z the complete conditional
tail cap, including Never. Actual punishment profiles starting immediately
after the finite cutoff produce

    b_z=max(E_z,A_z+h_z P_z)

by global minimality and the definition of the true punishment infimum.
The profile need not attain that infimum. Choosing a strict alleged gain
first, then punishment accuracy, then a sufficiently late realizing index,
is enough. No new test preceding the punishment is silently admitted.

Since d is nonatomic, its actual test gives A_z+h_z s_z. The bound
P_z≤max(s_z,0)=s_z therefore gives b_z=E_z. Replacing opponent ghosts by
Never makes the remaining z tests have maximum

    max(E_z,A_z+h_z s_z,A_z)=E_z.

Thus the SAME entire semantic pair is preserved. The finite approximation
forces z's vanishing late/Never remainder onto the old cutoff, with uniform
o(1) payoff and cap cost, before doing the exact off-path modification.
This is a lawful actual-source argument, not a nominal punishment value.

Uniqueness of the earliest owner now has an exact role: every other
zero-Never player has positive finite mass strictly after d, which becomes
positive Never mass. All opponents of z consequently have positive Never
mass in the reduced source. For each available b<d, every player still
survives to b with positive probability, so fixed-cut regeneration applies.

As b↑d, each opponent's conditional finite mass tends to zero, because its
numerator tends to its zero mass at d and its denominator is bounded below
by its positive new Never mass. Uniform bounded-payoff coupling gives

    b_z(q^b)≤s_z+2MΣ[j≠z] q_j^b(finite)→s_z.

Every q^b is nevertheless an actual global minimum and therefore satisfies
b_z(q^b)≥s_z+δ. This is the contradiction. It requires neither convergence
of z's own conditional law nor continuity of an unproved terminal debt at
a zero-survival limit. All later/tie/Never responses are included in the
uniform cap bound.

## Boundary falsification attempts

The sign restriction cannot be dropped from the stated ghost erasure.
For two players take r_0({0})=−1, r_0({1})=−2, r_0({0,1})=−1 and all
player1 rewards0. Let player0 have a diffuse clock before1 and player1
quit surely at2. Player0's old cap is−1. Replacing player1's ghost clock
by Never raises that cap to0 while leaving the prescribed payoff−1.
This is not a positive-minimum counterexample; it exactly tests the step
where max(s_z,0) cannot be replaced by s_z.

The nonatomic endpoint is also necessary for the displayed endpoint test.
If both players quit at d, with player0 rewards own singleton1, passive
singleton10 and pair0, then A_0=10 and h_0=0, but the d-test pays0, not10.
Thus E_0≥A_0+h_0s_0 cannot be asserted at a joint atom. The reviewed theorem
excludes all such atoms explicitly.

With two zero-Never players sharing d, the opponent conditional finite mass
in the last step need not tend to0. The argument does not claim otherwise.
Binding Never caps introduce no separate failure because they remain in
both the punishment and the post-erasure complete caps.

## Inspected source and significance

I inspected the literal declarations:

- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`:
  it uses a positive global SUM-debt carrier minimum and gives δ≤b_i−s_i;
- `quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`:
  the actual-profile infimum equals the carrier minimum;
- `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`:
  the bound is max(s_i,0), not s_i for arbitrary signed own rewards.

The new consumed content is the finite reachability of ANY fixed surviving
diffuse cut and its use after exact punishment-tail canonicalization. It
closes the unique-earliest diffuse source branch even when Never caps bind;
the strict-Never-buffer social-max dispatch alone did not do that. This is
an actual-minimum narrowing, not a new raw-table UE family or a completed
Fin4 proof. Its ordinary compact-source and prefix-erasure dependencies
remain explicit and are not claimed as checked Lean here.
