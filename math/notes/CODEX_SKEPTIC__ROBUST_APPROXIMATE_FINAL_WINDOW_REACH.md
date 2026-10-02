# A robust reached final window for approximate finite timing Nash

Author: CODEX_SKEPTIC.

## Status

Independent derivation from frozen Sections 1–11 of
`CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md`, completed before
reading RENY's independently added Section 12. The proof below derives a
uniform positive reach bound for every sufficiently accurate finite timing
Nash source in a hypothetical Fin4 game without a uniform-equilibrium
payoff. It uses the existing all-tolerances/all-charges forward-packet
compiler by contraposition and the actual support-pruning and payoff-floor
producers of RENY's note.

Comparison with RENY's Section 12 is now complete: the statements and all
packet fields agree, with different valid charge-to-survival estimates. No
mathematical objection was found. The separate review is
`feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_SKEPTIC.md`.

This is ordinary mathematics, not a newly Lean-checked theorem. It supplies
the previously conditional reach field; it does not consume the resulting
final window or prove an equilibrium. No export or Lean edit is made.

## 1. Complete statement

Fix four players, a reward table r on every nonempty quitting coalition with
|r_i(S)|≤M and M>0, independent private behavioral randomization, and zero
payoff if no player ever quits. Suppose this fixed game has no
uniform-equilibrium payoff. Let χ_i be its behavioral punishment value.

For deadline N, a finite timing ε-Nash profile means an independent product
of laws on {0,…,N−1,Never}, each player's gain from every replacement law
on that same finite menu being at most ε. This is ex ante Nash error, not
an unrestricted terminal-Nash hypothesis. Let q_i(t) be its literal hazard
realization, and

    c(t)=∏_i(1−q_i(t)),     R(t)=∏_{s<t}c(s).

Then there exist H≥1, e_*>0, and 0<ρ<1, depending only on the fixed game,
such that for every N≥H, every 0≤ε≤e_*, and every finite timing ε-Nash
profile p at deadline N,

    R(N−H) ≥ ρ.                                      (1)

This applies to every such source and imposes no bound on Nε. The reached
tail at date N−H is literally the conditional tail of that same source,
translated to a deadline-H timing profile; it is ε/R(N−H)-Nash and hence
(e_*/ρ)-Nash. Every original root before that cut has a common positive
Continue floor. The rounding used to prove (1) changes a prefix only in
the contradiction; it does not replace the source in the conclusion.

## 2. Inputs and exact consumer audit

The game has a global unrestricted terminal gap Γ>0 by
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
(`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`). Shrink Γ
if necessary so that η=Γ/(2M) lies in (0,1). RENY Section 5 supplies numbers
H_a≥1 and a_*>0 such that every finite timing a_*-Nash profile with deadline
at least H_a has every initial Continue probability at least η.

RENY Section 11 supplies, for every τ>0, H_f≥1 and f_*>0 such that every
finite timing f_*-Nash profile with deadline at least H_f has prescribed
payoff at least χ−τ coordinatewise. Its two source connections were checked
in their actual files:

- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`)
  supplies the all-player punishment-normality field;
- `IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable`
  (`UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`)
  applies to the bounded exact annotated limit spine and summable absorption.

The approximate source producers in RENY Sections 5, 10, and 11 remain
ordinary mathematical inputs here. The final consumer is the exact source
declaration

`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
(`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`).

For one fixed compact payoff carrier C it consumes

    ∀δ>0 ∀Q≥0, Nonempty(QuittingFiniteForwardPacket r C δ Q).

The record `QuittingFiniteForwardPacket` in the same file requires exact
prefix Bellman evaluation, support endpoint inequalities against the
continuation value, values in C, punishment floor χ−δ at every displayed
value including both endpoints, and total root absorption charge at least Q.
The definition `IsQuittingRootSupportApproxNash` was checked in
`UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`.
It is the unweighted support condition; no mixed-root error is substituted.

## 3. Fix the forbidden packet and all constants first

Take the canonical compact carrier C=[−M,M]^4. By contraposition of the
consumer and no uniform payoff, there are δ₀>0 and Q₀≥0 such that no
packet in C has support/floor tolerance δ₀ and charge at least Q₀.
Replacing Q₀ by any larger number preserves this prohibition. Fix one
forbidden Q≥1.

Set

    δ=δ₀/4,       τ=δ₀/4,
    a=η⁴,
    μ_* = min(1, δ₀/(16M)),
    ρ = exp(−(Q+2)/a).

Obtain H_f,f_* from the Section 11 floor producer at tolerance τ, and put
H=max(H_a,H_f). Choose e_*>0 small enough that

    e_* ≤ ρ a_*,
    e_* ≤ ρ a f_*,
    e_* ≤ ρ η δ,
    e_* ≤ ρ δ μ_*/4.                                (2)

Every right-hand side is strictly positive and depends only on the fixed
game and the preceding constants. A positive minimum suffices. There is no
deadline-dependent parameter or circular choice of reach.

## 4. First crossing gives a long controlled prefix

Assume for contradiction that an ε-Nash source with N≥H and ε≤e_* has
R(N−H)<ρ. Let K be the first integer t≤N−H with R(t)<ρ. Since R(0)=1,
K≥1, and R(t)≥ρ for every t<K.

At each such t, the conditional source is finite timing ε/R(t)-Nash with
remaining deadline N−t≥H. By (2), ε/R(t)≤a_*, so the initial-root theorem
applies to this literal conditional source and gives

    1−q_i(t)≥η,      c(t)≥a>0             (t<K).       (3)

In particular the crossing endpoint is reached and satisfies

    ρa ≤ R(K)=R(K−1)c(K−1) < ρ.                     (4)

Thus every displayed source value v(t), including t=K, is the actual
conditional payoff of a finite timing profile with remaining deadline at
least H_f. Moreover ε/R(t)≤ε/(ρa)≤f_*. The Section 11 producer therefore
gives

    v_i(t) ≥ χ_i−τ                       (0≤t≤K).    (5)

The factor a=η⁴ in this endpoint check is indispensable. A statement using
ε/ρ at t=K would not be justified by the first-crossing definition.

## 5. Crossing forces enough absorption charge

Write A=Σ_{t<K}(1−c(t)). For a≤c≤1,

    −log c = ∫_c^1 du/u ≤ (1−c)/a.

Consequently

    A ≥ a[−log R(K)] > a log(1/ρ) = Q+2.             (6)

Only the rootwise Continue floor was used to convert small survival into
large total charge. Small endpoint survival alone would not give (6),
because a single near-sure root could otherwise absorb almost all mass.

## 6. Actual pruning gives the forbidden packet

Apply RENY Section 10 once to the original prefix 0,…,K−1, using threshold
δ, source reach ρ, and source Continue floor η. Remove exactly the hazards
whose original Quit-minus-Continue endpoint difference is below −δ. The
suffix from K onward remains literally the original root sequence. The
total removed hazard satisfies

    μ ≤ 4ε/(ρδ) ≤ μ_*.                             (7)

Recompute every modified value v'(t) as the actual payoff of its literal
modified suffix. Exact chronological Bellman equations then hold. All values
lie in C, and support error before K is at most

    max(δ, ε/(ρη)) + 4Mμ ≤ δ₀/2 ≤ δ₀.               (8)

At every displayed value, (5) and the uniform payoff coupling estimate give

    v'_i(t) ≥ χ_i−τ−2Mμ ≥ χ_i−3δ₀/8 ≥ χ_i−δ₀.       (9)

At t=K, v'(K)=v(K) literally, so the estimate is especially direct; (4)
was what licensed its original floor. The total modified absorption charge
A' loses at most μ, so (6)–(7) imply

    A' ≥ A−μ > Q+1 ≥ Q.                             (10)

Now reverse the actual prefix:

    w(s)=v'(K−s)                  (0≤s≤K),
    x(s)=q'(K−1−s)                (0≤s<K).

Chronological Bellman evaluation v'(t)=F(q'(t),v'(t+1)) becomes exactly
w(s+1)=F(x(s),w(s)), which is the forward packet's source orientation.
Each x(s) is support-δ₀-Nash against w(s); all values lie in C and satisfy
χ−δ₀, including w(0)=v'(K). Reversal preserves the finite absorption sum.
Extend roots/values arbitrarily beyond the constrained prefix. These data
are a `QuittingFiniteForwardPacket r C δ₀ Q`, contradicting its fixed
prohibition. Therefore R(N−H)≥ρ.

## 7. Same-source information retained in the conclusion

For T=N−H the original source, not its hypothetical pruned replacement,
has the following fields:

- R(t)≥ρ for every 0≤t≤T, by monotonicity and (1);
- 1−q_i(t)≥η for every t<T, by conditional finite Nash and (2);
- the original suffix at T is an actual finite timing profile of deadline H
  with error ε/R(T)≤e_*/ρ;
- all its conditional entry payoffs through T satisfy χ−τ, using the same
  Section 11 parameters; and
- the behavioral laws, absolute cut T, and original opponent-deleted
  survival products are retained literally. No compactified terminal
  annotation is substituted for this reached suffix.

The proof gives no unrestricted small debt for that final H-date profile.
Its finite-menu Nash error does not cap the omitted after-deadline action.
Thus positive reach is supplied, but final-window consumption remains a
separate task.

## 8. Exact endpoint regression and remaining review

The factor η⁴ in (4) is sharp for the root data alone. Let η=1/2 and
ρ=1/8. One root with Continue probabilities (1/2,1/2,1/2,1) gives
R(1)=ρ. Follow it by a root with all Continue probabilities 1/2. The first
strict crossing is K=2 and

    R(2)=1/128=ρη⁴.

Exact Fraction arithmetic checked this example. It is a probability-only
endpoint regression, not a Nash source or a hypothetical-counterexample
table. It tests the denominator that the payoff-floor application requires.

No step sums K copies of the original Nash error. The only cumulative error
is the one-sided removed-hazard budget (7), which is why the constants do
not depend on K,N or Nε.

After saving Sections 1–8, I read RENY's Section 12. Its proof takes
−log R(K)≤(4/η)Σα_t by applying −log(1−q_i)≤q_i/η separately and using
q_i≤α_t. This is valid and sharper than the η⁻⁴ factor used in (6). Both
proofs choose all constants before the source deadline, explicitly apply
the endpoint floor using ε/(ρη⁴), preserve the final suffix under pruning,
and reverse the roots with their actual continuation values. I find no
omitted packet field or unresolved objection in Section 12. Section 13 and
the final-window consumer are outside this independent check.
