# Review of `SOFT_CYCLE_TROPICAL_LCP_AND_TWO_NEVER_ESCAPE`

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`  
Reviewed note SHA-256:
`a48d2ce92abadca6246228933722fe944effd304571337ca2d5137660b70b79d`

## Verdict

**PASS, with one required source-correspondence correction and two useful
proof clarifications.**  I found no counterexample to the mathematical
theorem.  The first-order singleton law, tropical complementarity, cap
limit, positive-clearance step, nonsingleton-support step, and the two
literal Never gains all survive independent reconstruction.

The source list should add
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalCorePunishmentNormal.lean`
and name
`all_punishmentNormal_of_normalCore_eq_univ`.  The declaration
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` alone
concerns the recursively defined matrix core; it does not by itself state
punishment normality.  The missing bridge is already checked, so this is a
source-handoff correction rather than a mathematical gap.

The H=1 proof should also name
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
from `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` for the
fixed positive terminal gap, and it would be clearer to say explicitly that
closedness is applied to the continuous expected two-action regret
`max(Q,C)-F`, not separately to unsupported endpoint inequalities.

## Claim checked

For a sequence of exact-return soft cyclic roots with

```text
H_n epsilon_n -> 0,
h_n=sum_(t,i) x_(n,t,i) -> 0,
lambda_(n,i)=sum_t x_(n,t,i)/h_n -> lambda_i,
```

the note claims:

1. the limiting payoff is the singleton lottery with weights `lambda`;
2. with `A_ik=r_i({k})-r_i({i})`, the vector
   `m=A lambda` satisfies the complementarity system
   `m_i>=kappa>=0` and `lambda_i>0 => m_i=kappa`;
3. checked aggregate endpoint regret divided by `h_n` tends to `kappa`;
4. for `lambda_i<1`, the unrestricted terminal cap tends to
   `max(r_i({i}),N_i)`, where `N_i` is the opponents-only singleton refusal
   value;
5. under the Fin4 no-uniform-payoff hypothesis, `kappa>0`, the support of
   `lambda` has size at least two, and two fixed support owners have literal
   Never gains bounded away from zero; and
6. choosing the producer with `H_n=1` forces the vanishing-total-hazard arm,
   because every positive isolated-owner limit is consumed by the checked
   punishment-completed solo-cycle theorem.

## Independent reconstruction

Let `X_(n,i)=sum_t x_(n,t,i)` and `h_n=sum_i X_(n,i)`.  The sum of all
same-stage collision probabilities is bounded by a constant times `h_n^2`,
and replacing every survival prefix by one changes total singleton mass by
the same order.  One-period absorption is therefore `h_n+O(h_n^2)`, and its
conditional absorbing law tends to the singleton lottery `lambda`.  The
phasewise Bellman oscillation is at most `2 M h_n`, so every phase value has
the same limit.  This proves the claimed payoff law.

Uniformly in phase,

```text
Q_(n,t,i)=s_i+O(M h_n),
C_(n,t,i)=v_i+O(M h_n).
```

Since every soft hazard is at most `h_n` and hence eventually below `1/2`,
the logit identity makes `C-Q` positive.  Thus every limit margin
`m_i=v_i-s_i` is nonnegative.  If `m_k>m_l`, comparison of the exact odds at
arbitrary phases gives

```text
x_(n,t,k)/x_(n,u,l)
 <= 2 exp(-(m_k-m_l+o(1))/theta_n).
```

After summation, the extra factor is at most `H_n`; it vanishes because
`theta_n log H_n -> 0`, a consequence of
`theta_n=epsilon_n/log 2` and `H_n epsilon_n->0`.  Hence positive limiting
mass can occur only at a minimum margin.  When the margins are positive, the
checked endpoint-regret summand is exactly `x_(n,t,i)(C-Q)`, so division by
`h_n` gives `sum_i lambda_i m_i=kappa`.

For `lambda_i<1`, deleting player `i` leaves one-period opponent absorption

```text
h_n(1-lambda_i)+o(h_n).
```

Conditional on that absorption, the singleton owner distribution tends to
`lambda_k/(1-lambda_i)` for `k!=i`.  A deterministic Quit time consists of
an arbitrary number of complete opponent periods, one partial period, and a
final Quit.  The partial-period absorption and final tie have total mass
`O(h_n)` uniformly in the chosen time.  Therefore every pure-time payoff is
within `o(1)` of a convex combination of `N_i` and `s_i`.  Quit immediately
and literal Never attain the two limiting endpoints.  The checked pure-time
extremality theorem then gives the unrestricted cap formula.

If `lambda_i>0`, complementarity gives `v_i-s_i=kappa`, while

```text
v_i=lambda_i s_i+(1-lambda_i)N_i.
```

Thus

```text
N_i-v_i=lambda_i kappa/(1-lambda_i).
```

For Fin4, nonexistence of a uniform payoff gives full recursive normal core
and excludes the homogeneous simplex branch.  Consequently `kappa=0` is
impossible.  A singleton support would force
`kappa=(A e_i)_i=A_ii=0`, so at least two owners have positive mass.  Each
such owner has `lambda_i<1` and a strictly positive limiting Never gain.
Choosing two support labels and then one common positive lower constant gives
the claimed two fixed debtors.

For the final H=1 reduction, the checked global-gap equivalence and the
soft-cycle debt estimate select a fixed debtor `i` whose three opponents'
one-row absorption tends to zero.  Hence all opponent hazards tend to zero.
If the remaining owner hazard tends to `p>0`, the root and value converge to
the positive-rate solo root and `r({i})`.  Continuity of
`max(Q,C)-F` transfers exact endpoint Nash to this limit.  The checked
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
followed by the separately checked
`all_punishmentNormal_of_normalCore_eq_univ` supplies

```text
quittingPunishmentValue reward i <= r_i({i}).
```

The hypotheses of
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR` are
then exact, contradicting nonexistence.  Therefore `p=0`, and the preceding
vanishing-hazard theorem applies.

## Falsification regressions

1. **Punishment normality cannot be omitted.**  On `Fin 4`, designate player
   `0`, put `r_0({0})=-1`, put every other payoff to player `0` equal to
   zero, and set `r_j({0})=r_j({0,j})=0` for `j!=0` (the remaining
   coordinates may be zero).  Every positive-rate solo row owned by `0` is
   exact endpoint Nash against continuation `r({0})`.  Nevertheless literal
   Never guarantees player `0` payoff zero against every opponent plan, and
   all opponents Continue gives cap zero, so its punishment value is
   `0>-1`.  The solo-cycle compiler's punishment hypothesis fails.  This
   does not contradict the theorem: player `0` is outside the recursive
   normal core, and the table itself has the all-Never equilibrium.

2. **Fixed H is essential in the isolated-owner reduction.**  With periods
   tending to infinity, an owner's mass may be spread as atoms of order
   `1/H`; the positive per-period absorption survives while every individual
   collision opportunity vanishes.  This is exactly the singleton-diffusion
   regression already recorded in the reviewed producer.  The H=1 choice
   removes that escape.

3. **Positive clearance and two owners are sharp.**  If the normalized solo
   matrix has a homogeneous simplex solution, `kappa=0` and every formula
   above gives zero limiting refusal debt.  If a complementary limit has
   singleton support, the zero diagonal forces `kappa=0`.  Hence neither the
   positive-debt conclusion nor two distinct debtors survives after dropping
   the no-homogeneous hypothesis.

4. **The exclusion `lambda_i<1` in the cap theorem is necessary.**  At a
   single-owner limit the opponents' absorption is lower order than `h_n`,
   so division by `1-lambda_i` is meaningless and the Never limit can depend
   on the next scale.  The note correctly postpones this case to the H=1
   solo-arm argument.

## Scope

This PASS covers the ordinary-mathematics theorem at the frozen hash and its
claimed unrestricted deviation scope.  It does not claim that the resulting
two-Never object has a checked consumer, prove the reverse S.3 implication,
or turn the source-attached debts into a uniform equilibrium.  The final
two-cut/nonvanishing-order bridge remains open exactly as the note states.

## Exact-hash delta verdict

I rechecked the repaired frozen note at SHA-256
`3b53c80a8803c182544e2e919132e7d5ce9d9264924bb7418df8b5886bbeab69`.
**Delta PASS.**  The added source entry names the exact missing bridge
`all_punishmentNormal_of_normalCore_eq_univ` and correctly distinguishes the
recursive alpha core from punishment normality.  The added joint-closedness
source `isClosed_isεQuittingRootEndpointNash_simplex` has exactly the required
topology in tolerance, tail payoff, and simplex root, so it validates the
vanishing-error solo-root passage used in Theorem 4.1.  The control-character
scan is clean.  These repairs resolve the required source objection without
changing the theorem or its scope; my mathematical PASS covers this exact
hash.

## Standalone export-candidate verdict

I independently checked
`/tmp/FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md` at exact SHA-256
`7a4fd1f67bab58b3398d6cfb54150b5c90c9feaa32b0283ab293d5ae0e9a3132`
against the repaired reviewed source note at SHA
`3b53c80a8803c182544e2e919132e7d5ce9d9264924bb7418df8b5886bbeab69`.
**Standalone/delta PASS.**  I found no mathematical, source, scope, link,
formatting, or control-byte objection.

In particular, the candidate preserves the weighted endpoint inequalities at
the possible boundary `p=1`; the joint closedness declaration applies to the
vanishing tolerance, singleton tail, and simplex root simultaneously.  It
routes full recursive core through
`all_punishmentNormal_of_normalCore_eq_univ` before invoking the solo-cycle
compiler, and it uses the full-core identification before excluding an
ambient homogeneous simplex solution.  The cap proof is uniform over every
finite pure time and literal Never, so the cited pure-time extremality theorem
really does cover escaping clocks and arbitrary behavioral deviations.  The
positive clearance and zero diagonal force at least two support owners; two
labels are fixed after one finite subsequence and their literal Never gains
have one common positive eventual floor.

The paired-matrix test is correctly presented as a positive-clearance
noncontradiction with a separate periodic consumer, not as a counterexample.
The outsider-lift regression correctly limits zero outsider debt to the
unchanged soft source and does not claim it survives replacement by an
arbitrary smaller-game equilibrium.  All nine mandatory export headings are
present.  Every relative link resolves from the proposed `exports/` location,
the control-character scan is clean, and `python3 ../scripts/check_docs.py`
passes on the current repository.

## Citation-only candidate delta

I verified the corrected staged candidate at exact SHA-256
`6a4e7c3fb5d0e8af44b76e4d4aed8d08365a5c61c7787da808f3877a358eba02`.
**Delta PASS.**  The corrected path
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` is the
actual defining file of
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`.  This is a
citation-only repair from the PASSed SHA `7a4fd1f...`; the mathematical body
and scope are unchanged.  All links resolve, the control scan is clean, and
the documentation check passes.  My standalone mathematical PASS covers this
exact hash.
