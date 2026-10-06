# Independent bounded check of the complementary-odds degree producer

Reviewer: CODEX_MORSE.

Scoped verdict: **PASS** on the root-production mechanism and its actual-
game adapter in the final section “Global nonlinear degree supplies the
missing nonzero root” of
`../notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, whole-note SHA256
`e11cbd808d6c55b858dbf1a65d00a24a073472d6353ca3195b8f56e0357bca7e`.
I reconstructed the degree argument and challenged its signed and boundary
cases independently, without another review. This is ordinary mathematics,
not a Lean build. No full new-coverage fixture audit or export-artifact
verdict is included in this bounded check.

## Raw hypothesis and strategic scope

For one partition into two pairs, the assumptions are exactly

    c_i=r_i({i,a(i)})−r_i({a(i)})>0,
    r_i({i}∪T)≤s_i for every nonempty T in the opposite pair.

There is no sign restriction on own levels, Π_i, K_i, or the singleton
matrix. The construction under full R₀ and nonzero R₀ degree supplies
a nonzero complementary odds vector, possibly on a face, and from it an
exact original-game period-two terminal Nash profile. Bare Fin4 no-UE
supplies R₀ and degree one, so the contradiction proves raw UE existence.
Neither an inverse cone nor a chosen favorable component is an input.

## The global feasible-set bound

Let E={X≥0:ΓX≥N(X)}. In a proposed unbounded sequence normalize by
t=ΣX and take a nonzero limit u. Choose u_j>0 and i=a(j). The identity

    N_i=c_iX_j(X_k+X_l)+(c_iX_j−K_i)X_kX_l
          +Π_iX_j²/(1+X_j)

is exact. Since X_j tends to infinity, the second coefficient is eventually
nonnegative, whatever the sign of K_i. The last term has absolute value
O(t), whatever the sign of Π_i. Thus u_k>0 or u_l>0 would give a
positive order-t² lower bound incompatible with ΓX=O(t). The normalized
support is contained in the scheduled pair {i,j}.

The next limit uses the actual zero diagonal Γ_ii=0. Dropping the first
two nonnegative terms gives Γ_ij u_j≥Π_i u_j, whereas
Γ_ij=Π_i−c_i<Π_i and u_j>0. This is a contradiction even if both
coordinates of the limiting pair are positive. No positivity of N, of
the inverse, or of every original coordinate of the sequence was used.
The closed feasible set E is therefore compact.

## Total degree and the local origin

For H_λ(x)=min(x,Γx−N(x⁺)−λ1), a zero necessarily has x≥0,
nonnegative residual and complementarity. It therefore belongs to E for
every λ≥0. Since ΓX−N(X) is bounded on E, a sufficiently large finite
Λ leaves H_Λ with no zeros. A ball containing E in its interior gives
one common zero-free boundary for λ∈[0,Λ]. Hence the total degree of
H₀ in that ball is zero. This does not incorrectly extrapolate a local
degree or assume properness of the whole ambient map.

Under R₀ the positively homogeneous minimum map h(x)=min(x,Γx) has
only the zero root. Its norm has a positive minimum on the unit sphere,
so ‖h(x)‖≥a‖x‖. Meanwhile N(x⁺)=O(‖x‖²). The uniform perturbation
bound for coordinatewise minimum makes
min(x,Γx−θN(x⁺)), 0≤θ≤1, nonzero on a sufficiently small sphere.
Consequently the origin has the nonzero homogeneous R₀ degree. Excision
against the total degree zero forces another root outside that small ball.
No differentiability, regular-root census or isolated nonlinear root
assumption is present.

I inspected `r0Degree` and
`localDegree_lcpMinBoxProblem_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0Degree.lean`. The source uses the homogeneous
minimum-complementarity map and its positively oriented scalar chart;
the sign and radius identification needed here is the literal one.
Only nonvanishing is needed for the contradiction.

## Singleton supports and actual inactive values

If only X_j>0, all N_l vanish except possibly at i=a(j). Feasibility
forces Γ_lj≥0 outside that mate row. The remaining inequality is

    Γ_ij≥Π_iX_j/(1+X_j).

For Π_i<0 it is impossible because Γ_ij=Π_i−c_i<Π_i, while the
right side exceeds Π_i. For Π_i≥0 it forces Γ_ij≥0 too. Thus any
feasible singleton support would give a nonzero homogeneous LCP solution,
contradicting R₀. The produced root has at least two positive coordinates.

The template endpoint identities are correct with arbitrary Π,K:
active Continue equals U_i and passive Continue equals W_i+e_i/D_i.
For X_i=0, solving the actual two-phase recursion gives

    W_i^act−W_i=(e_i/D_i)/(1−(1−q_a)/D_i),
    U_i^act−U_i=(1−q_a)(W_i^act−W_i).

The denominator is positive because there is a positive opponent hazard.
Both corrections are nonnegative. Active forced Quit equals U_i, while
passive forced Quit is at most s_i≤W_i. Thus the correct actual values,
not the potentially incorrect template values, give every inactive
player's incentives. Positive coordinates have e_i=0 and retain the
original active equalities. All deleted-opponent cycles contract, giving
the unrestricted behavioral and fixed-target horizon conclusion by the
usual finite-iteration remainder argument.

An exact adversarial point combines all three delicate features. Use the
two-cycle-plus-leaves Γ displayed earlier in the note, schedule 01/23,
and take

    s=(1,1,1,1), Π=(2,2,−1/4,−1/4), K=(7,7,0,0),
    X=(1,1,0,0).

Then c=(1,1,1/4,1/4), e=(0,0,1/2,1/2), and U=W=(2,2,1,1).
The actual two inactive values are instead 7/6 at both phases. Their
correction is (1/8)/(3/4)=1/6. All cross-pair participant and relevant
triple rewards can equal their caps 1, so this is compatible with a
complete original table. The example tests negative Π, positive K,
boundary support and nonzero inactive correction at once. It is not
offered as new-coverage evidence.

## Literal source and weak boundary

`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
does supply full R₀ and degree one from the original no-UE hypothesis,
without singleton-sign or auxiliary-equilibrium assumptions. Its named
R₀ dependency in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`
matches the stated matrix. Therefore the actual profile closes the
strict raw Fin4 argument, not only a conditional root interface.

The weak c_i≥0 extension also checks as UE-only reward closure: adding
δ to the four scheduled participant entries changes neither singletons
nor any opposite-pair joining cap. It makes every c_i strict. Applying
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
then returns an original-game fixed target. An exact periodic profile at
the weak boundary is not obtained from that argument and is not claimed.

I found no failed implication in this mechanism. The proposed modified
coverage table still requires its own complete source/child audit, exactly
as the author states; this scoped PASS does not certify that separate
unfinished task or authorize an export.

The author confirmed that whole-note hash
`80edfc39db0bd72f1c2ead9bea17552d89d4357c6e81bffeb6913a209076d44b`
changes only introductory/current-status text from the reviewed hash. I
reread the final degree section at those bytes; it is unchanged, so the
same scoped mathematical PASS applies. Later appended examples or coverage
claims are not included automatically in this mechanism verdict.
