# Independent review of geometric compression and simultaneous pivot repair

Reviewer: CODEX_HILBERT.

Reviewed input: `gpt/GEOMETRIC_COMPRESSION.md`, all396 lines, SHA-256
`a710fb8d255a60af4a564bc921c0bb0668716233e7120b2f1d6c9dffcd138b19`.

Verdict: mathematical PASS for the complete packet. No substantive repair
was found. This is ordinary mathematical review, not Lean verification or
permission to self-export. I read the entire original before any other
review and did not read RENY's review. The example's reward data were read
directly from `gpt/EXACT_EXAMPLE.md`; its separate uniqueness proof was not
used as an input to this review.

The new exact statement is a simultaneous one-player repair optimization,
not an arbitrary-game producer. The fixed-three-law infimum is a finite LP
value; its optimizer need not be an actual strategy at a boundary. The outer
optimization over three finite stopping laws remains unsolved and generally
nonconvex. Export assembly should replace references to the previous answer
by the complete reward table or a stable explicit source, and state Never=0,
independent laws, unrestricted behavioral deviations, and the finite-menu
index convention in one self-contained statement.

## 1. Exact compression and the full response class

Fix any three laws supported below N or at Never. An arbitrary pivot law is
split into its exact atoms before N, late finite mass λ, and Never mass ν.
When λ>0, countability and well-ordering give a FIRST positive late atom
α>0. Its date t* may be arbitrarily later than N. Thus h=α/λ belongs to
(0,1], and the proposed geometric law is literal, including h=1.

The prescribed coalition law is exactly preserved, not merely approximated:
if another player stops before N, only the pivot's unchanged finite head is
relevant; otherwise all three opponents are at Never, and only the pivot's
late finite versus Never mass matters. No public coupling is implemented.
The altered object is one independent marginal stopping law.

For a nonpivot j, let A_j be the unconditional early reward against its
opponents when j continues through the finite head, and let
d_j=Π[ℓ≠0,j]p_ℓ(Never). With a_j=r_j({0}), b_j=r_j({0,j}), the complete
payoff of pure Quit t≥N is exactly

    A_j+d_j[a_j Pr(N≤T₀<t)+b_j Pr(T₀=t)].

The remaining event gives j its own singleton zero. The geometric formula
is a convex combination of A_j+d_j b_j α and A_j+d_j a_j λ. The former
is the OLD response Quit t*, because no earlier late pivot atom exists; the
latter is the OLD response Never. This includes negative a_j or b_j,
zero d_j, ν>0, and preemption before a pivot atom. No sign assumption on
spectator or collision rewards was used.

All responses before N are unchanged. Never is unchanged too. Hence every
new pure response is bounded by the old cap. Taking mixtures covers EVERY
behavioral response, not merely current Quit/Continue endpoints. The exact
source declaration `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
in `Quitting/Cycles/BehaviorPureTimeExtremality.lean` has precisely this
unrestricted scope and was read in place. The pivot's cap is unchanged
because its opponents are unchanged.

The brief noncanonical extension is also correct. For own singleton s_j,
the late expression becomes

    A_j+d_j[s_j(λ+ν)+(a_j−s_j)F_t+(b_j−s_j)f_t].

The new finite responses interpolate the old first-late response and the
limit of old finite responses, while Never is retained separately. Thus
three old cap-bounded endpoints suffice. This extension does not silently
justify using the canonical TWO-endpoint LP for arbitrary singleton rewards.

## 2. LP value, implementation, and the genuinely nonliteral boundary

For fixed opponents, Q_t, W₀, D₀, and the pivot cap are constants. Every
nonpivot early pure payoff π_j,t and A_j is affine in the pivot head and
the late/Never masses. The formulas for U_j are therefore affine. The full
nonpivot cap is exactly the maximum in equation11: finite early responses,
Never, and the first geometric late response. Later geometric responses
introduce no additional inequality. This verifies all LP constraints.

The case λ=0 is literal with α=0 and no late tail. If 0<α≤λ, the optimizer
is implemented exactly. If α=0<λ, there is NO probability law with positive
late finite mass and zero first positive late atom. Keeping all other
coordinates fixed and taking α'>0 tending to zero preserves every prescribed
payoff; each new cap is at most its boundary value plus Mα'. Consequently
the LP optimum equals the infimum over ALL pivot behavioral replacements.
It is not asserted to be an attained behavioral optimum.

Nonattainment is real, not just a formal concern. Fix all three opponents
at Never. Set r₀({0})=1, r_j({j})=r_j({0})=0 and r_j({0,j})=1 for each
nonpivot j, completing other entries arbitrarily. The boundary point
λ=1,ν=α=0 with zero head has LP value0. Every actual proper pivot law has
a positive finite atom, at which a nonpivot gets a profitable collision
deviation. A pivot law with positive Never mass instead has positive pivot
debt. Thus the fixed-opponent repair infimum is0 and is unattained, while
geometric laws of hazard tending to zero approach it. This verifies exactly
the distinction maintained by the packet; it does not challenge equation13.

For fixed opponent data the LP minimum exists: the probability variables
lie in a compact polytope, and the objective can equivalently be written as
the continuous maximum of the displayed finitely many gains and zero.
No compactness of the original unrestricted strategy optimization is assumed.

## 3. Actual truncation, menu, and absorption quantifiers

After K geometric atoms at N,...,N+K−1, the remaining finite mass is
β=λ(1−h)^K. Moving exactly this mass to Never changes the pivot marginal
by TV=β. The prescribed payoff of any player changes by at most2Mβ.
Every nonpivot response payoff changes by the same bound uniformly over
the response law, so its cap changes by at most2Mβ. The pivot cap changes
by zero. Hence the common unrestricted exploitability bound4Mβ is valid.
It does not require a horizon-dependent sum of stage errors.

The implemented/truncated law is supported strictly below N+K, together
with Never. For any nonnegative integer H it is therefore an actual law
on the menu of deadline L=N+K+H. At date L−H=N+K its joint survival is
exactly D₀(ν+β), including the old Never mass ν. Equation15 follows from

    B₀−U₀
      =Σ[t<N]μ_t(B₀−Q_t)+λ(B₀−L₀)+ν(B₀−W₀)
      ≥νD₀,

since B₀≥L₀=W₀+D₀. This uses DELETED survival D₀, not the original
prescribed joint reach. The final reach bound z+β is valid even when the
source's original prescribed reach was zero or some deleted factor is zero.
Approximating α does not change this pivot inequality.

There is no requirement to restore exact finite-menu Nash. The bound is
against unrestricted deviations already, and therefore against every
displayed finite menu containing the law. K can be increased to meet any
additional lower deadline requirement while decreasing β. If no geometric
tail is present, take β=0 and display the unchanged finite law on a larger
menu directly. The packet's finite-menu consumer has the claimed agency
and quantifiers.

## 4. Independent exact check of the example and its two repairs

With opponents at τ with probabilities4/7 and1/7, respectively, and dummy
Never, the pivot's early, date-τ, late-finite, and Never response values are

    1, 217/49, 235/49, 217/49.

Thus its arbitrary-law debt is (186u+18v+18n)/49. Direct conditioning gives
player1's gain from Never as (−20v+176w+8n)/49. Their convex combination
with weights98/107 and9/107 is precisely

    [1584+16644u+252n]/5243.

Since full exploitability bounds each of the two gains, this is a genuine
all-pivot-strategy lower certificate. It remains valid at τ=0, where u=0
automatically; permitting early dates does not weaken it.

At the proposed optimizer v=88/107, w=19/107, h=1/2, I independently
enumerated the eight active first-coalition outcomes with exact rational
arithmetic and used the geometric late-response endpoints. The results are:

| Player | U | Full cap B | Full debt |
| --- | --- | --- | --- |
| 0 | 23561/5243 | 235/49 | 1584/5243 |
| 1 | 35117/5243 | 7 | 1584/5243 |
| 2 | 35498/5243 | 7 | 1203/5243 |
| 3 | 31/49 | 31/49 | 0 |

For additional checks, the date-τ pure values are31/7,4847/749,4040/749,
and−4901/5243. The nonpivot late caps are7,7,31/49, respectively. Thus
equation20 verifies every full response, not merely the two lower-bound
witnesses. The reported decimal1584/5243≈0.302117 is correct.

Player1's first Never replacement is an actual full best response of value7
against the unchanged other laws. Afterward player2's Never value is7;
its early singleton is0, its collision payoff with the pivot is5, and every
late geometric response interpolates a collision endpoint with its Never
payoff. Thus the second replacement is also a full best response.

After both replacements, player1 remains safe: its date-τ value is
8·88/107=704/107<7, and each later response equals
7·88/107 plus19/107 times a convex combination of4 and7. Player2 is safe
by the corresponding collision value5, the dummy cannot gain from joining,
and the proper pivot receives its full singleton cap1. The exact terminal
payoff is (1,7,7,0). The two-step argument relies on these table entries;
it does not establish a general monotone best-response procedure.

## 5. Exact conjecture-facing reduction and source overlap

The clean equivalence is:

    arbitrarily small full-regret finite four-law profiles
      iff
    arbitrarily small z*(p₁,p₂,p₃) for finite opponent laws.

For the forward direction, use the original finite pivot head, λ=α=0 and
its original Never mass as a feasible LP point. Its objective is the actual
full regret, so z* is no larger. For the reverse direction choose a sufficiently
small LP value, approximate a zero-α boundary if needed, and truncate with
β small. Equations14–16 supply an actual finite product law with small full
regret and the required small final-window reach. Thus one unrestricted
strategy choice has really been eliminated into a finite LP. The remaining
three-law optimization is not itself linear: its coefficients contain
independent opponent products and the pivot cap is a maximum of such values.

The narrow production-source check found the following existing ingredients:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `Quitting/Cycles/BehaviorPureTimeExtremality.lean`: exact all-behavior cap
  reduction, including Never.
- `quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le` and
  `quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max`
  in `Quitting/Terminal/FiniteDeadlineFullReplyCap.lean`: the old single late
  candidate when ALL displayed laws are finite.
- `singlePivot_nonpivot_fullCap_eq_menuCap` and
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
  `Quitting/Terminal/SinglePivotFiniteMenuSource.lean`: the canonical scalar
  discrepancy for a supplied finite product law.
- `exists_elementaryCompressedProfile_terminalSemantics_close` in
  `Quitting/Terminal/TailCompression/ElementaryTailSemanticReduction.lean`:
  approximate full-profile semantic compression by elementary tail caps.
  Its statement changes an entire tail after a chosen cutoff and approximates
  payoffs/caps; it does not fix three given marginals and exactly preserve
  all payoffs while decreasing all caps.

These definitions and declarations were read in place. A targeted search
for geometric compression, simultaneous pivot repair, first late atom, and
pivot repair LP in the relevant quitting subtrees found no existing matching
declaration. The exact geometric domination and fixed-opponent LP are thus
not already supplied by the inspected finite-menu or elementary-compression
APIs. This is a bounded source-overlap assessment, not a claim of a complete
literature or Lean-tree novelty survey.

The source-strength change is useful and precise, but stops before a UE
producer: arbitrary opponent laws are supplied to the inner LP, and no theorem
selects three laws whose LP value vanishes. The packet says so accurately.

## 6. Final whole-assembly confirmation

Assembly checked in full: all603 lines of
`notes/CODEX_RENY__GEOMETRIC_PIVOT_COMPRESSION_EXPORT_DRAFT.md`.
Exact SHA-256:

    eefbd41c7d599398e39fd669322e010709ad60a294e02e21e191efbea2fce46d

The entire substring from `## Exact statement` through EOF independently
hashes to:

    7688fc8c6f4def05a4e897f41fd9274f13153087856dde2d7439d6df59c15551

Verdict: final assembled statement/proof surface PASS. This is correspondence
and extension checking after the two original independent full reviews,
not a third proof gate. I did not read RENY's original review. No substantive
repair is requested; the pending-confirmation header may be updated without
changing the reviewed mathematical body.

The expanded signed LP was explicitly checked, not treated as automatically
covered by the original canonical LP. For nonpivot own singleton c_j, its
late finite value is

    A_j+d_j[c_j(λ+ν)+(a_j−c_j)F_t+(b_j−c_j)f_t].

The three endpoints C_j, Z_j, W_j are therefore precisely those in the
assembly. Z_j need only be a limiting old finite response, not an attained
one. The pivot's signed cap correctly retains BOTH W and W+gD as well as
the head candidates. All LP expressions remain affine in the inner variables.
The boundary perturbation changes only C_j, by at most2Mα; the canonical
Ma estimate remains a separate specialization. These formulas also cover
one player, λ=0, ν>0, h=1, zero deleted survival, and signed rewards. The
signed boundary test correctly requires its third endpoint Z_j=1/2 even
though C_j=W_j=0.

The positive-g assumption occurs exactly where needed for absorption:
νD≤z/g. The all-zero countertest correctly refutes applying that reach
deduction when g=0, not the compression or signed LP. The e,H,ρ,N₀
construction uses a literal finite law and L≥max(N+K+H,N₀), so both its
menu and the identity R(L−H)=D(ν+β) are verified. It makes no nested-profile
or exact-menu-Nash demand.

The full numerical table is now included. I checked the added early and
first-late cap entries against the previously derived exact values, including
the dummy's3146/5243 first-late payoff and both additional Never-repair
endpoint calculations. The complete reward table also makes the stated
nonattainment example self-contained. The geometric COMPONENT versus the
actual hazard with ν>0 is now explicitly distinguished.

Theorem4 is the exact canonical source equivalence requested: the existing
finite scalar source, arbitrarily small three-law LP values, and actual
finite full-regret/early-absorption profiles with every displayed parameter
are equivalent. Its proof does not assume the unresolved small-value source.
The inner LP is finite convex optimization; no corresponding outer convexity,
attainment, effective deadline, or universal existence is asserted.

The stable intake link exists and identifies the original submission hash;
its wrapper has its own different file hash, as expected. The newly explicit
general-PMF TV declaration was checked in
`MathUE/ProbabilityMassFunction/GeneralTotalVariation.lean`, and the fixed-
payoff terminal-all-errors endpoint was rechecked in
`Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Their quoted scopes agree with the assembly. The handoff section labels
suggested interfaces as suggestions, and no new Lean seal or general UE
claim is present.
