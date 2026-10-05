# Independent falsification review of the signed four-cycle producer

Reviewer: `CODEX_FRECHET_CYCLE`.

Status: the stated sufficient producer passes this whole-proof mathematical
audit. No unresolved mathematical objection was found. This is ordinary
mathematical review, not a Lean check, an unrestricted strategy-class
completeness theorem, or a literature-priority determination.

Reviewed submission:
[`CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER.md`](../notes/CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER.md),
SHA-256
`1c63777ff44e26b9e7784de334b15db905f8c0ce09fa649a1317b7394f0ba330`.
The entire submission was read before any feedback. No other review of this
submission was read. The argument below was reconstructed independently,
including attempts to break the small-eigenvalue choice, the phase floors,
the Never comparison, finite censoring, and the coverage claim.

## 1. Claim and probability model checked

There are four players with independent Continue/Quit randomizations at the
unique live state. The first nonempty quitting coalition absorbs and has its
specified four-coordinate reward; infinite all-Continue has payoff zero.
There are no public signals, correlated recommendations, or deviation
detection. A unilateral deviation can replace the player's entire behavioral
strategy, with no time or memory bound.

For arbitrary own singleton levels and arbitrary rewards on the eleven
nonsingleton coalitions, the displayed strict conditions on the twelve
off-diagonal singleton comparisons produce one fixed payoff vector. For each
positive accuracy a profile realizes that target and satisfies the uniform
finite-horizon contract against every behavioral deviation. The separate
finite output quantifies over every `e > 0`, `H ≥ 1`, `ρ > 0`, and `N₀ ≥ 0`,
and produces a product law on a finite menu with full terminal exploitability
below `e` and survival at `N − H` below `ρ`.

This is a sufficient raw-data construction on a specified open class. The
hypothesis does not supply a cycle, hazards, a tail, an equilibrium, or a
punishment. It makes no claim to represent all games or all equilibrium
payoffs.

## 2. Spectral branch and all four balance equations

Write `u = (W₀,W₁)`. The displayed discriminant is exactly the discriminant
of the characteristic polynomial of `K`. Hence the selected smaller root
`λ` is an eigenvalue. Direct multiplication gives

```text
(K₀₀ − λ)(−K₀₁) + K₀₁(K₀₀ − λ) = 0,
−K₁₀K₀₁ + (K₁₁ − λ)(K₀₀ − λ) = det(K − λI) = 0.
```

The imposed signs make both entries of `u` strictly positive. The two further
tests make the reconstructed `W₂,W₃` strictly positive. This uses neither
Perron positivity nor the dominant eigenvalue. In particular, testing the
larger eigenvalue of the base matrix gives `(78,−26)` in the same eigenvector
formula, so replacing the smaller root by a Perron-style choice would break
the construction.

From the last two reconstruction equations one gets

```text
W₂ = A[(d₁ + a₁a₂)W₀ + a₁d₂W₁],
a₀W₂ + d₀W₃ = A(XW₀ + YW₁) = W₁.
```

Substitution in `a₃W₁ + d₃W₂`, using the last equality, gives the first row
of `A K u = u`, and therefore gives `W₀`. This proves all four equations
(2.1), with no sign restriction on the individual `aᵢ` used in the algebra.
Multiplication by the positive `bᵢ` gives the four rotated balance equations
(2.3). For the last row canceling `A` is legal because `λ > 1`.

Normalization gives positive `wᵢ`, total mass `1 − A < 1`, and
`tₖ = A + Σ[j ≥ k]wⱼ`. Thus `tₖ > wₖ > 0`, all four hazards and survival
factors are strictly between zero and one, and their survival product
telescopes to `A`. There is no hidden zero denominator or zero-survival
boundary.

## 3. Actual values and every phase floor

The period is almost surely absorbing. Its value at phase zero is exactly
`Σwⱼr({j})/(1−A)`. Starting after phase `i`, the stated rotated one-period
weights have total `1−A`; the multiplier for entries before the cut is
exactly `A`. Dividing the balanced comparison sum by `(1−A)tᵢ₊₁` proves
`vⁱ⁺¹ᵢ = sᵢ`. Bellman at phase `i` then proves `vⁱᵢ = sᵢ`.

The remaining two phases can be checked without any assumption on the
opposite comparison:

```text
0 = −qᵢ₊₁ bᵢ + cᵢ₊₁(vⁱ⁺²ᵢ − sᵢ),
vⁱ⁺³ᵢ − sᵢ = qᵢ₊₃ hᵢ + cᵢ₊₃(vⁱᵢ − sᵢ).
```

These are precisely the two strict floors in (3.2). Together with the two
equalities they cover all sixteen player/phase entries. Negative opposite
comparisons do not invalidate an unexamined interior floor. Every player
also has three positive opponent hazards per period.

These data meet the exact fields of `BalancedSingletonCycleCertificate`
in `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`:
owner, hazard, coarse values, initial phase, probability bounds, Bellman arc,
active equality, solo floor, and opponent divergence.

## 4. Full deviations, fixed target, and collision stress test

For a phase subdivided into `L` dates, put `c = cᵢ` and let `m` dates remain.
The value there is

```text
(1 − c^(m/L))r({i}) + c^(m/L)vⁱ⁺¹,       0 ≤ m ≤ L.
```

It lies on the segment between the two coarse endpoints: the coefficient
of `vⁱ` is `(1 − c^(m/L))/(1 − c)`, which belongs to `[0,1]`.
Consequently every floor holds on the full fine mesh, including endpoints,
and the owner remains exactly indifferent.

For fixed deviator `j`, replace its choices by Continue before a finite date
`t`, then restore its prescribed strategy. At a `j`-owned date this replaces
a mixture of two equal values by one of them; at every other date `j` was
already continuing. Backward substitution therefore preserves the original
date-zero payoff exactly. Quitting at `t` instead of restoring can gain at
most `2M max θᵢ` conditionally on survival to `t`. Its date-zero gain has
the additional opponent-only reach factor, which is at most one. This is a
single stopping gain, not a sum of local errors over time.

For Never, the opponents' survival after `K` whole fine periods is
`(∏[i ≠ j]cᵢ)^K`, tending to zero. Comparing Never with forced Continue
through these periods and then restoration leaves an absolute payoff error
at most `2M(∏[i ≠ j]cᵢ)^K`. Thus Never has exactly the prescribed payoff,
including when own singleton levels are negative.

At every reached live date the observed history is the unique all-Continue
history. A complete behavioral deviation induces a probability law on its
first Quit date in `ℕ ∪ {Never}`; its terminal payoff is the mixture of the
corresponding pure-date/Never payoffs against the independent opponent
clocks. The uniform pure-date bound therefore covers all behavioral
deviations. No restriction to finite-support mixtures or bounded controllers
has entered.

An adverse completion checks why the coarse exact-Nash claim would be false.
For `Γ†`, take `sᵢ = 1` and set `r₀({0,1}) = 3`. Player zero can Continue
at date zero and Quit at date one. With the coarse hazards `1/2`, the latter
date pays `3` if player one also quits and `1` otherwise, so its payoff is
`2` instead of the prescribed `v⁰₀ = 1`. This does not refute the submission:
it explicitly avoids coarse exact Nash, and subdivision reduces this gain
to `2θ₁`. It also shows why the neighboring exact-root-Nash compiler cannot
be invoked on the produced coarse data for arbitrary collision rewards.

The target is unchanged by subdivision. The cited
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` has exactly
the required fixed-target conclusion. I also inspected its underlying
`singletonArcCycle_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`: it chooses one
mesh per accuracy and obtains one profile valid at every sufficiently long
horizon. It does not substitute the separate horizon-indexed square-root
family for the uniform quantifiers.

## 5. Finite censoring and early absorption

Each player's independent clock survives `K` full fine periods with mass
`cᵢ^K`. Mapping all its remaining finite times to Never therefore changes
that marginal only on an event of that probability. Under the product
coupling, some prescribed clock changes with probability at most
`δ = Σcᵢ^K`. Since every terminal payoff, including Never, lies in `[-M,M]`,
every prescribed payoff changes by at most `2Mδ`.

For a fixed pure deviation, couple only its opponents. This gives a payoff
change at most `2MΣ[i ≠ j]cᵢ^K ≤ 2Mδ`, uniformly over every finite date,
including dates after the cutoff, and over Never. Taking a supremum is
therefore legitimate. Full exploitability of the censored profile is at most

```text
2M max θᵢ + 4M Σcᵢ^K.
```

The choices in the submission make this strictly below `e`. The censored
joint Never mass is exactly `∏cᵢ^K = A^K`, and there are no finite atoms at
or after `T = 4LK`. With `N ≥ T+H`, survival at `N−H` is consequently
`A^K < ρ`. One can take `N = max(T+H,N₀)`. All requested quantifiers and
strict inequalities are met. Enlarging the menu is sound because deviations
at every later finite time were included in the coupling estimate.

## 6. Independent exact fixture checks and matrix placement

Exact rational recomputation with SymPy, used for arithmetic verification,
gave the following discriminants and reconstructed hazards:

| Table | Discriminant | Eigenvalues, increasing | Hazards |
| --- | --- | --- | --- |
| `Γ*` | `4225` | `16, 81` | `(1/2,1/2,1/2,1/2)` |
| `Γ†` | `388129/100` | `16, 783/10` | `(1/2,1/2,1/2,1/2)` |
| `Γ‡` | `3600` | `12, 72` | `(1/3,1/2,1/2,1/2)` |

The three displayed `K` matrices, all four reconstructed values at every
phase, all owner equalities, and every floor agree exactly with the
submission. The determinants are `−1200`, `−2319/2`, and `−781`. The three
displayed inverse formulas multiply their respective matrices to the
identity, and every inverse entry is strictly positive. These finite checks
support the fixtures; the general identities were proved separately above.

If `B = Γ⁻¹ > 0` entrywise and `x ≥ 0` is nonzero, some diagonal term
`Bᵢᵢxᵢ²` is strictly positive and every term in `xᵀBx` is nonnegative.
Hence `B` is strictly copositive. The applicable source theorem is
`isStandardQMatrix_of_copositive_of_isR0Matrix` in
`UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`;
the strict-copositivity consequences are also explicit in
`IsStrictlyCopositive.isR0Matrix` and
`isStandardQ_of_strictlyCopositive` in
`MathUE/LinearProgramming/CopositiveQCorollaries.lean`.

The inversion argument has the correct sign and variables: a `B`-solution
at `−Bq` has nonnegative variable `w`, residual `z = B(w−q)`, and
`wᵢzᵢ = 0`. Multiplication by `Γ` gives `w = q + Γz`, so `z` is a
`Γ`-solution at `q`. This proves all-right-hand-side standard-Q, not a
directional screen. For homogeneous `w = Γz`, complementarity gives
`0 = zᵀw = wᵀBw`; strict copositivity forces `w = z = 0`. Thus no
homogeneous simplex solution exists.

For the opposite principal, write it as `[[0,−u],[−v,0]]` with `u,v > 0`.
At `q = (−1,−1)` its projective residuals are `−α−uy` and `−α−vx`.
Nonnegativity forces `α=x=y=0`, contradicting total mass one. The
projective obstruction is stronger than failure of a standard LCP here:
the zero-cemetery branch is explicitly excluded too.

The definition `normalLayer` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean` retains
row `i` when it has a distinct retained `j` with `Γᵢⱼ ≤ 0`. The successor
is such a witness. Induction keeps the full four-player set at every layer,
so the claimed recursive normal core is correct. This does not identify that
algebraic core with a separately defined punishment/minmax normal set.

## 7. Openness and genuinely heterogeneous source scope

All denominators and every selected inequality are strict at both
heterogeneous fixtures. The discriminant stays positive, the chosen simple
eigenvalue and reconstructed coordinates are continuous, and strict inverse
positivity persists while the determinant remains nonzero. Preserve one
strictly negative opposite pair as well. Their intersection gives an open
neighborhood in the twelve off-diagonal coordinates lying in the claimed
full-core, standard-Q, nonhomogeneous, non-projective-Q-bar regime.
The four own levels and forty-four nonsingleton reward coordinates remain
free. The theorem does not require positive own levels; choosing all four
equal to one also avoids the already solved zero-solo case.

The narrow source comparison supports the stated novelty boundary:

- `hasQuittingCanonicalEqualHazardTailData_iff` in
  `UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`
  requires a cyclic singleton matrix. The base fixture has closed tail
  `(0,0,2,6)` at survival `1/2`, so its coverage is already present.
- `CyclicSingletonTailData` in
  `UniformEquilibrium/Quitting/Cycles/CyclicSingletonTailProducer.lean`
  has a single tail indexed by relative phase and a single survival factor.
  Rearranging its recurrence gives
  `Γᵢⱼ = tail(j−i) − c tail(j+1−i)`, forcing cyclic invariance.
  Therefore the heterogeneous examples are not merely instances of this
  existing input with an overlooked choice of tail.
- `Γ†` cannot become cyclic even under relabeling and positive row scaling:
  row zero has two unequal negative magnitudes, while the other rows have
  equal negative magnitudes. The ratio of the larger to the smaller
  negative magnitude is `10/9` in row zero and `1` in the other rows.
  This ratio is invariant under positive row scaling and independent of
  column order. Equality of these ratios across all rows is necessary for
  a scaled cyclic matrix. Their strict separation persists in a smaller
  neighborhood of `Γ†`. Thus the noncirculant open neighborhood can itself
  be kept outside this enlarged cyclic input class.
- Every row of these examples has two strictly negative off-diagonal
  entries. Hence no player order can meet
  `QuittingCyclicSingletonOpenSignData`, which permits just its first
  forward comparison to be negative.
- The additional raw producer
  `exists_certificate_of_unitOutneighbor` in
  `UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`
  requires `Γ = tournamentSkewMatrix t A` for an integral tournament and
  `t > 1`. The opposite entries of such a matrix are `t` and `−1`.
  A mutually negative opposite pair excludes this class under every
  relabeling and positive row scaling. The exclusion is open.
- `BalancedSingletonCycleCertificate.exists_escortCycle` is a necessity
  result for supplied certificates. The theorem
  `isUniformEquilibriumPayoff_of_finitePlayerPhaseNashCertificate` in
  `UniformEquilibrium/Quitting/Cycles/CyclicKofNPlayerPhaseHazards.lean`
  takes supplied hazards and exact phase root-Nash conditions. Neither is
  a raw heterogeneous producer that supplies the data here.
- The nearby `IsQuittingBlockCertificate` in
  `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` and
  `HasSolvedExactQuittingCycle` in
  `UniformEquilibrium/Quitting/Cycles/ExactCycleStrata.lean` likewise
  package supplied cyclic Bellman/Nash data. The interior approximate
  blocks in `EndogenousInteriorCyclicBlock.lean` do not assert a terminal
  or uniform-payoff result at arbitrary local error. No subsuming raw
  singleton producer emerged from this bounded comparison.

The explicit formula therefore adds a sufficient heterogeneous raw-data
class relative to these relevant existing inputs. This is more than verifying
a supplied cycle. The comparison does not assert that every nonsingleton
completion of the fixtures was previously unsolved: some arbitrary
completions can also satisfy other sufficient equilibrium criteria. Nor does
it prove a global repository or literature priority claim. The submission's
final formulation respects those limits.

## 8. Source discipline and final disposition

The route was selected through `docs/TOOLKIT.md`, with the existing
balanced-singleton and cyclic-tail declarations as the first dependencies.
The exact target was checked in `quittingUniformEquilibriumPayoffConjecture`
in `UniformEquilibrium/Quitting/Conjecture/Basic.lean`. Matrix row/sign and
projective conventions were checked in `quittingSingletonMatrix`,
`StandardLCPSolution`, `ProjectiveLCPSolution`, `IsProjectiveQBarMatrix`,
and `normalized_singletonMatrix_eq_quittingSingletonMatrix` in the
corresponding `QuittingRewardAdapter.lean`, `MatrixClasses.lean`, and
`Normalization.lean` files under
`UniformEquilibrium/Quitting/Classification/LCP/`.

The literature lane's `README.md` and the Section 5 transcription in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean` were inspected
only for the projective-Q/Q-bar convention and the stated scope of the
continuous-path sufficient condition. No paper theorem is used as an
unchecked behavioral adapter, and no paper-priority conclusion is drawn.
The original paper was not independently reread in this audit. The source
declarations were inspected under their imports; no Lean build was run.

Valid: the full sufficient producer, the fixed uniform target, the
unrestricted finite/Never deviation estimates, the literal finite early
absorption construction, all exact fixtures, the matrix placement, and the
heterogeneous open neighborhood with the source-scope qualifications above.

False claims found in the frozen submission: none. The coarse exact-Nash
strengthening is false by the collision example in Section 4, but the
submission explicitly does not claim it. The dominant-eigenvalue replacement
also fails and is explicitly avoided.

Unresolved mathematical objections: none. No export or author-note edit was
made. The concrete next check is external formalization of the raw
`K,λ,W` reconstruction into the existing balanced-singleton certificate,
retaining the smaller root and the two signed floor identities exactly.

## 9. Final assembled-surface confirmation

I read the complete final assembled packet
[`HETEROGENEOUS_SIGNED_SINGLETON_FOUR_CYCLE_PRODUCER.md`](../formalized/HETEROGENEOUS_SIGNED_SINGLETON_FOUR_CYCLE_PRODUCER.md),
including its exact statement, semantics, source comparison, full proof,
boundary examples, adapter, proposed formalization, and nonclaims. I did not
read the other review. The verified full-file SHA-256 is

```text
b6ef2d02ffcfe4f6c1cdfb71cff09d59dea09c2e4bca418970d4e712dfbfdc84
```

The verified SHA-256 of the bytes from `## Exact statement` through EOF is

```text
a11e68a1345dfee4125179b601768749becf87c508ad493e427b4c686adfdb9d
```

Verdict for this exact final surface: PASS, with no unresolved mathematical
objection. The theorem preserves the original sufficient hypotheses and
conclusions and incorporates the qualifications from this review. In
particular, it distinguishes new raw-data input coverage from a claim that
every reward completion was previously unsolved.

The added elementary uniform-horizon argument is valid. For fixed mesh `L`,
the event of survival under any deviation is contained in the event that
all nondeviating opponents survive. Its probability after `K` periods is
therefore at most `β^K`, with `β < 1` independent of the deviation. Grouping
the survival sum into periods bounds the expected absorption time plus one
by `4L/(1−β)+1`. The stated average/terminal error bound is conservative
and uniform over all responses. Choosing mesh first, then a common horizon
threshold, preserves exactly the required quantifier order. I checked the
definition `Game.IsUniformEquilibriumPayoff` in
`GameTheory/GameTheory/Stochastic/Uniform.lean` as well.

For the expanded source comparison I additionally inspected the definitions
of `QuittingPureSingletonChamber`, `QuittingPurePairChamber`,
`QuittingInducedOwnerChamber`, `IsQuittingConditionalFaceGapRange`, and
`IsStrictFiniteOddBlockerCore` in the files named by the assembly. Their
collision restrictions, supplied induced Nash data, reward-range bounds,
and passive-payoff identities do not follow simply by leaving all
nonsingleton coordinates free. I also inspected the ordinary non-Q input,
`exists_uniformEquilibriumPayoff_of_homogeneousMatrixBranch`, and
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in the assembly's
named matrix-branch sources. No new whole-class subsumption was established.

The proposed Lean names are clearly marked as proposals, and the packet
does not claim that the new producer is already Lean-checked. This
confirmation authorizes no changes by the reviewer to the author notebook
or export directory; neither was edited.

### Administrative final-byte update

The assembly subsequently changed only its review-status header and replaced
the obsolete question-reference paragraph by the identical standalone finite
early-absorption conclusion. I inspected both replacements. Reversing just
those two literal replacements in a read-only stream reproduces the earlier
verified full-file hash `b6ef2d02ffcfe4f6c1cdfb71cff09d59dea09c2e4bca418970d4e712dfbfdc84`.
This independently verifies that no other bytes changed.

PASS with no unresolved mathematical objection therefore also applies to
the final full-file SHA-256
`8dabb5e019ed9542f76058b1ae34919791c510117226e1cdae3cf0de5b1d9e33`.
Its exact-statement-to-EOF SHA-256 is
`8bf4e37b4a59bd02fc9c466ee60aa60909739ca4a8d87d554981d82d7a9a9cd7`.
The proof-section hash remains
`2140dd418fdc9ec046837029f7629da26f70d1bbc15819bdfe2daacbd225a809`.
No other review was read during this update.
