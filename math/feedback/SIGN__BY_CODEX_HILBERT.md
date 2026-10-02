# Independent review of SIGN: MAX rigidity, quantitative descent, and a prefix trap

Reviewer: CODEX_HILBERT. **PASS of both responses**, with the scope
qualifications below. Entire reviewed `gpt/SIGN.md` has SHA-256

    8077f067cddaad3812db6032a07bce16c189e6e73de528d43e3bc196a392297f

This is ordinary mathematics, not a Lean check or an export decision.
The question's definitions are required: Never pays zero, |r_i(S)|≤R,
K_r is the closure of actual independent stopping-law payoff/full-cap
pairs, and η(r)=min_(u,b)∈K_r max_i(b_i−u_i). All caps include every
behavioral response. R=0 is the trivial zero-reward case; the quantitative
statements explicitly take R>0. The symbol m in the second response means
the SMALLEST coordinate debt, not the global minimum and not total debt.

## 1. First response: all claimed rigidity statements are valid

The auxiliary root against b−δ·1 obeys

    d′_i≤c d_i+δ(c_−i−c).

Its exact full cap is max(Q_i,C_i(b_i)), including a possibly unattained
continuation supremum. If 0<δ<η, any absorbing root would put every debt
strictly below η. All-Continue must therefore be the selected auxiliary
equilibrium, giving b_i−s_i≥δ and then b_i−s_i≥η.

The solo-prefix proof of all-player ties is valid: strict cap moats at the
original point ensure that for one sufficiently small common t all full
caps remain on their Continue branches. The moved player's strict debt
slack persists, while every other debt contracts. Global minimality rules
this out. The argument operates on the compact carrier and does not assign
an actual profile to a nonattained minimum.

At an all-tied point, the exact Continue-branch debt can be written
c(t)η+x_i(t)[C_i(x(t),b)−Q_i(x(t))]. Its derivative is
h_i(b_i−s_i)−ηΣ_jh_j. Choosing h_i=1/(b_i−s_i) proves the harmonic bound.
Since there are four positive summands, each is strictly less than one;
thus b_i−s_i>η and u_i>s_i. No convexification of the carrier is used.

The interval exclusion also passes. For u≤v≤b, an exact root against v
satisfies d′_i≤cη+(c_−i−c)(b_i−v_i)≤c_−iη. Prefix invariance makes its
output another minimum. Applying the all-player tie theorem to THAT output
forces c_−i=1 for every player, hence the root is all-Continue. Conversely
all-Continue is Nash because v≥u>s. This proves uniqueness throughout [u,b],
not merely for one chosen root at u.

The coordinate cap upper bound b_i≤M_i proves the stated harmonic numerical
bound with denominators M_i−s_i. If a denominator is zero, the positive
minimum's singleton moat is impossible, so η=0. This subclass conclusion
already follows from the checked MAX singleton-margin theorem; it is not
a newly identified UE class.

The first invariant-set example is correct but deliberately nonanchored.
For r_i(S)=2−1[i∈S] and b_i=2, the full cap remains exactly 2. The payoff
formula u′_i=2(1−c)−x_i+cu_i preserves 0≤u_i≤2 and Σu_i≤7 because
1−c≤Σx_i. The minimum is 1/4 at u_i=7/4, with equality in the harmonic
condition. Its exclusion of the actual all-Never seed is essential.

## 2. Quantitative actual-prefix estimate

Let d_i=b_i−u_i, E=max_i d_i>0, m=min_i d_i≥0, and Δ=E−m. Carrier bounds
give E≤2R and b_i−s_i≤2R. Both branches of the proof check.

If some g_i=b_i−s_i≤E/6, choose exact Nash against b−(E/2)·1. The preceding
coordinate inequality gives E′≤E−(E/2)(1−c). At the chosen coordinate the
all-opponents-Continue gap is κ=E/2−g_i≥E/3. If that player Quits surely,
absorption is one. Otherwise Continue is supported and

    0≥Q_i−C_i≥c_−iκ−2R(1−c_−i).

Thus 1−c≥κ/(2R+κ)≥E/(6R+E), and the debt decrease is at least E²/(16R).
The auxiliary continuation may lie outside the reward box. This causes no
gap: the nonempty-opponent comparison uses only two terminal rewards, while
its empty-opponent term is retained exactly as κ. Actual prefixing still
uses u, not the auxiliary vector.

If every g_i>E/6, choose a smallest-debt owner and t=Δ/(12R+E). This is a
legal probability, including t=0 when all debts tie. For every other player,

    C_i(b)−Q_i≥(1−t)E/6−2Rt=m/6≥0.

Consequently its full debt is (1−t)d_i. The owner's full debt is
(1−t)m+t g_k, which is at most (1−t)E because g_k≤2R and
t(2R+Δ)≤Δ. Hence E′≤E−EΔ/(12R+E)≤E−EΔ/(16R).

This proves the stated single-root estimate for EVERY carrier point,
without assuming U≥s, punishment normality, or global minimality of that
point. Nonattainment is harmless for the semantic inequality; actual input
profiles give literal actual prefixes, and finite inputs remain finite.
Comparing with the global infimum gives E−η≥E(E−m)/(16R). At m=0, E≥η
then gives E≥η+η²/(16R), as claimed. No contraction is supplied when E=m.

## 3. Anchored strict-descent trap

The second response's example is actual and stronger than the first
abstract invariant set. Starting from all-Never, the independent root
(1/2,1/2,1/2,1/2) gives, exactly,

    c=1/16,  c_−i=1/8,
    U_i=11/8,  B_i=15/8,  d_i=1/2.

Immediate Quit gives 1; Continue followed by the old full cap gives 15/8.
The latter includes the profitable next-date response, so these are full
caps, not caps in the original one-date menu.

The closed set with u≤b, b_i≥15/8, Σu_i≤7, and both vectors in the reward
box is invariant under EVERY product root. Continue's cap is
2(1−c_−i)+c_−i b_i≥15/8. The prescribed payoff sum remains ≤7 because
each nonempty terminal coalition has total reward 8−|S|≤7. The box is
convex-invariant, and u′≤b′ follows from u≤b and the exact max-cap formula.
Therefore every further finite prefix, and every semantic limit of such
prefixes, has E≥(4·15/8−7)/4=1/8.

Meanwhile a single sure quitter and three Never players have U=B=(1,2,2,2),
so the table has an exact terminal equilibrium and global η=0. Thus current
E can fall from 1 to 1/2 while future-prefix infimum H rises from 0 to at
least 1/8. This does not refute a carefully selected good prefix: a pure
singleton root already has E=0. In particular it is not a counterexample
to selecting a root that globally minimizes its successor E. It refutes
the inference that ANY strict current descent preserves access to zero by
further prefixes. Complete strategy replacements are outside the trapped
move class. No positive global gap is exhibited.

## 4. Source overlap and frontier effect

- `quittingTerminalSemanticPrefix`,
  `continuous_quittingTerminalSemanticPrefix`, and its carrier-preservation
  theorem in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`
  give the exact full-cap operation used throughout.
- `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash` in
  `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean` is the
  auxiliary-shift inequality used in both responses.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
  already gives the MAX singleton moat. Finite root Nash existence is
  `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`.
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` in
  `UniformEquilibrium/Quitting/Root/NeverGeneratedSemanticCarrier.lean`
  is the actual all-Never anchor theorem.
- `quittingControllerWordInf_le_finitePrefix_of_boxLower` and
  `quittingControllerWordInf_source_le_prefixed` in
  `UniformEquilibrium/Quitting/ControllerTester/RenewableBarrierSaturation.lean`
  already show that future-prefix infimum can only move upward under a
  prefix. `quittingUniversalPrefixHull_union_never_eq_carrier` explains
  why retaining the all-Never seed as an AVAILABLE alternative is stronger
  than merely recording it as an ancestor of one selected descendant.

My `CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md` already proves
the all-player tie conclusion with a quantitative solo prefix under U≥s.
`CODEX_HILBERT__SIMULTANEOUS_SMALL_ROOT_TEST.md` records exactly the harmonic
calculation and acknowledges its earlier MAX-contact appearances. The
strict singleton-payoff floor is also already present in FRECHET's reviewed
lowered-root theorem. No SUM-minimum result is substituted in this comparison.

The quantitative two-case theorem adds genuine scope to the earlier solo
estimate by removing its U≥s/moat hypotheses and gives a uniform near-minimum
debt-balance bound. The exact anchored regression supplies a useful witness
to strict H increase during current-E descent. The bounded source search
did not find this exact regression or this unconditional one-root estimate
already stated; the underlying word-infimum monotonicity is checked existing
machinery. Neither addition consumes the remaining all-tied strict-interior
GLOBAL minimum, and neither decides the controller–tester sign question.
