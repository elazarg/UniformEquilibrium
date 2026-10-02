# Joint pair re-equilibration and the missing mixed head account

Identity: CODEX_TARSKI_PREMIUM.

## Status and concrete result

Ordinary mathematics, not independently reviewed or Lean-checked. No export.
This changes TWO complete finite laws jointly at the original source while
retaining the other two original laws. It is not a tail-only repair, a
two-marked-response replacement, or a quiet extension of a child equilibrium.

The construction makes BOTH changed owners' unrestricted debts small. A
single enlarged-calendar multiplier certificate then gives an exact
alternative: an untouched owner's near-active gain increases, or the
weighted mixed two-law term is substantially negative. The latter is the
joint head contribution absent from the separate first-order comparisons.
Neither alternative is yet a full-regret descent theorem.

Subsequent source comparison records the existing all-player-tie constraint:
under the positive-minimum hypothesis, vanishing pair debts force an
off-pair cost separated from that minimum. This is NOT a counterexample to
a desired source-to-near-minimum pair theorem; proving such a theorem under
the same hypothesis would give the desired contradiction. Section 5 keeps
this distinction explicit. Intermediate joint mixtures are a less
restrictive construction to test next, while retaining all four full caps.

Section 5a performs that intermediate test. It eliminates all response-
dependent mixed coefficients of the TWO repaired owners, but not those
of the untouched owners. The exact full-cap crossing conditions are
retained. Neither pair Nash existence nor the coupled source certificate
currently orients their common crossing interval. This is a stopped
comparison, not a new sufficient-condition wrapper or a no-go theorem.

The pair construction has a table-UNIFORM finite calendar extension at
every positive accuracy. Consequently it can be put on NOETHER's coupled
reward/profile certificate by choosing that extension before the calendar
window; the old adjacent-only certificate cannot simply be reused. The
comparison does not require replacing NOETHER's weights by FRECHET's
silent-prefix weights.

## 1. Probability model and the actual pair producer

There are four players, independent complete stopping laws on Nat∪{Never},
rewards r_i(S) for every nonempty first-quitter coalition S, and reward zero
at Never. Assume |r_i(S)|≤M, M>0; singleton signs are arbitrary. Write
U_i for terminal payoff, B_i for the cap over ALL behavioral replacements,
d_i=B_i−U_i, and E=max_i d_i. Pure finite dates and Never compute that cap.

Let X_N be the product of simplices on A_N={0,…,N−1,Never}. Its complete
tester set is T_N={0,…,N,Never}. Fix ANY μ∈X_N and a pair J={j,k}.
The two laws μ_l, l∉J, must remain literally unchanged.

**Pair producer.** For every ε>0 there is a finite L≥N and an actual
ρ∈X_L such that

    ρ_l=μ_l (l∉J),        d_j(ρ)≤ε, d_k(ρ)≤ε.          (1)

This is an unconditional producer, not a supplied-pair verifier. Its proof
uses the established two-player theorem only for the genuine induced tail
game on J, with reward r_i(S), i∈J, ∅≠S⊆J, and Never still zero.

Choose an actual two-player terminal ε-equilibrium σ of that induced
game. Form a finite two-player normal-form HEAD game. Each strategic player
has actions 0,…,N−1 and ⋆. Action t means Quit at that original date;
action ⋆ means Continue through the head and then follow σ_i shifted by N.
The frozen outsiders independently use exactly their original μ_l. The
payoff of every head action pair is its actual terminal expectation in
the four-player table. In particular this integrates all original outsider
same-date coalitions, not an artificial absorption payoff independent of
the head actions. Finite mixed Nash existence gives two independent head
mixtures x_j,x_k and hence actual laws ρ_j,ρ_k.

Every response before N is already an action of the head game. Fix i∈J
and consider any complete response after N, including Never. If someone
else stops before N, this response and ⋆ have the same outcome. Otherwise
the two outsiders both chose Never and the other strategic player chose ⋆.
This event has probability

    c_i=x_(J\{i})(⋆) ∏_(l∉J) μ_l(Never).

The payoff difference from replacing ⋆ by that late response is exactly
c_i times its deviation gain against σ_(J\{i}). It is at most c_i ε≤ε.
The head Nash inequality bounds ⋆'s payoff by U_i(ρ). Taking the full
response supremum proves (1). No source survival is assumed positive or
divided out. The all-Continue terminal event continues to pay zero.

Equivalently, one may solve the head backwards through finite 2×2 games.
At each stage, average r_i(A∪S) over the outsiders' current coalition S
when the strategic quitting set A is nonempty. When both strategic players
Continue, include the outsiders' absorbing contribution plus their joint
Continue probability times the next actual continuation payoff. These are
ordinary finite root games; zero-reach outsider rows may be defined
arbitrarily without changing any original outcome. This explains why bare
two-player existence alone was not enough without the head adapter.

For a finite output choose σ finite from the outset: start with a smaller
terminal error and move sufficiently remote finite marginal mass to Never.
The resulting uniform coupling bounds are at most 2M times the sum of the
removed masses for payoff and cap, hence at most 4M times that sum for
complete regret. Thus σ can be finite with error at most ε. If σ uses
dates below T, the construction gives L=N+T. No exact finite-menu Nash
approximation theorem for the original quitting game is invoked.

## 2. One uniform extension for all tables and all six pairs

For fixed M and ε>0 there is a FINITE T=T(M,ε) such that every signed
two-player table in [−M,M]^6 has a terminal ε-equilibrium using dates below
T and Never.

Proof: for each table a, the preceding two-player existence and finite
truncation give a finite profile with complete regret at most ε/2. For a
fixed actual profile, both payoff and cap are 1-Lipschitz in the raw table
sup norm; the full maximum regret is 2-Lipschitz. This same profile has
regret below ε for every table in an open ball of radius ε/4 around a.
The compact six-dimensional reward cube has a finite subcover. Take T to
be the maximum of those finitely many support lengths, at least one.
There is no claimed effective rate or constant optimization here.

All induced pair tables lie in this cube. Therefore, for EVERY r in the
bounded four-player reward cube, every N and μ∈X_N, all SIX sets

    Q_J(μ,ε)={ρ∈X_(N+T): ρ_l=μ_l for l∉J,
                              d_i(ρ)≤ε for i∈J}       (2)

are nonempty. They are compact, since all COMPLETE finite tester gains
are continuous polynomials. In particular one may minimize the ORIGINAL
full E over each entire Q_J, or over their finite union. This existence of
joint selection is not a proof that its selected value is small.

The extension is chosen before the multiplier below. The same certificate
then tests EVERY member of EVERY Q_J, not six independently chosen dual
certificates. Never mass is unrestricted and may change for the pair.

## 3. One original-source certificate and the full mixed term

Let μ∈X_N, e=E(μ), and L≥N+T. Retain all testers a=(i,t), t∈T_L.
An optional labelled zero row has gain and derivatives zero. Suppose ONE
probability λ on these rows satisfies

    Σ_a λ_a[e−g_a(μ)]≤a₀,
    Σ_a λ_a Dg_a(μ)[q−μ]≥−b₀  for EVERY q∈X_L.        (3)

Here g_(i,t)=V_(i,t)−U_i and a₀,b₀≥0. Source-inactive and after-support
testers remain in (3). Let θ_i be the total mass on owner i and
Θ=θ_j+θ_k. The zero row has no owner.

Fix ANY ρ∈Q_J(μ,ε). There are four actual product-law corners p^00=μ,
p^10=μ[j←ρ_j], p^01=μ[k←ρ_k], and p^11=ρ. Put

    A_a=g_a(p^10)−g_a(μ),
    B_a=g_a(p^01)−g_a(μ),
    C_a=g_a(ρ)−g_a(p^10)−g_a(p^01)+g_a(μ),
    C_λ=Σ_a λ_a C_a.

At EVERY independently mixed intermediate profile with marginal weights
α,β∈[0,1], the exact gain is

    g_a(α,β)=g_a(μ)+α A_a+β B_a+αβ C_a.               (4)

This is a gain identity, never an identity for the maximum of gains.
Since (q−μ) changes only j,k when q=ρ, (3) gives
Σλ(A+B)≥−b₀. No separate first-order weights are selected.

All responses owned by j or k at the JOINT endpoint have gain at most ε.
Their weighted total loss from the source is therefore at most
−Θ(e−ε)+a₀. Subtract it from the complete change in (4). The result is
the exact source-level lower bound

    Σ_(a owned outside J) λ_a[g_a(ρ)−g_a(μ)]
          ≥ Θ(e−ε)+C_λ−a₀−b₀.                        (5)

This consumes BOTH pair debts, not two marked responses. It also keeps
the joint term C_λ; summing the separate law derivatives would lose it.

More directly, when Θ<1 it gives the full-objective comparison

    E(ρ) ≥ e + [Θ(e−ε)+C_λ−a₀−b₀]/(1−Θ).           (5a)

Indeed G_λ(μ)≥e−a₀ and (4) imply
G_λ(ρ)≥e−a₀−b₀+C_λ. At the endpoint the pair-owned portion is at most
Θε and every other row is at most E(ρ), so
G_λ(ρ)≤Θε+(1−Θ)E(ρ). This proves (5a) without replacing a full maximum
by a weighted sum: the weighted sum is used as its legitimate lower
bound, while BOTH pair-owned complete envelopes have already been solved.

For a cutoff ζ>0, discard only source gains below e−ζ. Their total mass
is at most a₀/ζ, and any gain change is bounded by 4M. If

    D=Θ(e−ε)+C_λ−a₀−b₀−4M a₀/ζ > 0,              (6)

then some untouched owner l and complete tester t satisfy

    g_(l,t)(μ)≥e−ζ,
    g_(l,t)(ρ)−g_(l,t)(μ)≥D/(1−Θ).                  (7)

The positive numerator forces Θ<1. An optional zero row cannot be the
selected row because its gain change is zero. In particular the entire
endpoint then has E(ρ)≥e−ζ+D/(1−Θ).

If Θ=1, (5) instead immediately forces

    C_λ≤−(e−ε)+a₀+b₀.                                (8)

For example, when Θ≥θ₀>0, e stays bounded below, ε,a₀,b₀→0, and ζ→0
with a₀/ζ→0, every such pair endpoint has the following exhaustive
alternative: C_λ is negative by at least roughly half Θ(e−ε), or an
untouched near-active owner suffers a gain increase bounded below by a
positive constant. No arbitrary solved-profile example replaces these
source hypotheses.

In particular, if δ≥0 and E(ρ)≤e+δ, exact rearrangement gives

    C_λ≤−Θ(e−ε)+(1−Θ)δ+a₀+b₀.                       (9)

For Θ=1 this is also (8). Thus near-nonincreasing repairs with vanishing
source and pair errors require C_λ≤−Θ(e−ε)+o(1), without a cutoff loss.
Negative mixed curvature is NECESSARY, not sufficient: (4) still retains
the other full tester rows.

This has a genuinely two-law size consequence. Let
v_j=TV(ρ_j,μ_j) and v_k=TV(ρ_k,μ_k), with TV in [0,1]. Every fixed
gain is an expectation of a kernel bounded by 2M. Integrating its mixed
difference against (ρ_j−μ_j)⊗(ρ_k−μ_k) therefore gives

    |C_a|≤8M v_j v_k,       |C_λ|≤8M v_j v_k.         (9a)

The signed measures have total-variation norms 2v_j and 2v_k; this proves
the bound directly, including owner-j and owner-k testers. Hence the same
finite endpoint must satisfy

    8M v_j v_k ≥ Θ(e−ε)−(1−Θ)δ−a₀−b₀.             (9b)

If Θ has a positive floor, BOTH changed laws must move by a positive
amount in TV. A large repair of one owner plus a vanishing-total-mass
helper cannot kill both full debts and stay near the original full value.
This is not a bound in the weaker CDF metric, and no such replacement of
TV by CDF distance is asserted.

## 4. Actual global provenance and the coherent reward-window variant

For FRECHET's source, start with a genuine global finite-calendar minimizer
of full E, then use its literal silent prefix under the positive singleton
cap margins. If the original calendar is K, its head length is N=K+1.
Choose T(M,ε) first and an enlarged L≥N+T. The enlarged linearized-chord
proof is dimension independent and applies verbatim with

    R=√(192M(η_K−η_L)),       a₀=b₀=R.

Its Taylor bound depends only on four changed coordinates, not on the
number of dates. The global floor is η_L, not η_K. The same date-zero
screening proof then gives its all-owner lower masses for this λ. If
η_K→m>0, R→0 even when the selected L grows rapidly, because
0≤η_K−η_L≤η_K−m. Thus (5)–(9) apply simultaneously to all six constructed
pair families on the ORIGINAL source. No cap-preserving limiting law is
assumed.

NOETHER's different source keeps an outer reward normal and enlarged
profile stationarity with the SAME softmax weights. Its original note
controls only X_(N+1); that certificate is not substituted here. For a
PRESELECTED extension B=T(M,ε), use one common complete tester pool through
L=2m+B for all calendar minima in a window N=m,…,2m. The identical
source softmax derivative proof gives an X_(N+B) error

    R_N=√(2H[f_N−f_(N+B)]),      H=96+256/τ

for the normalized reward cube. Since the same sequence f_N is decreasing,

    Σ_(N=m)^(2m) [f_N−f_(N+B)] ≤ B(2+τ log q),

and its averaged derivative error is at most
√(2H B(2+τ log q)/(m+1)). Choose the window size AFTER B; for fixed B,
τ=m^(−1/2) makes both errors vanish. A diagonal choice handles ε→0 and
growing B(ε). The same source tuples and their reward-gradient average
remain in the outer normal calculation. This is the required enlargement
argument, not an identification with FRECHET's multipliers.

No all-owner bound is needed to apply (5) in that variant: the labelled
zero row satisfies λ₀≤a₀/e, so some owner has mass at least
(1−a₀/e)/4. Choose a pair containing that owner. Eventually Θ≥1/8 in a
positive-gap regime. Thus at least the three pairs containing that owner
have a uniform pair-weight floor under the ORIGINAL coupled certificate.

## 5. Literal raw-reward account and exact unresolved use

Let P_p(S) be the first-quitter coalition mass. Apply Δ_jΔ_k to the four
actual corners above. Then

    C_λ=Σ_(i,S≠∅) r_i(S) K_i(S),
    K_i(S)=Σ_t λ_(i,t)
       [Δ_jΔ_k P_(p[i←t])(S)−Δ_jΔ_k P_p(S)].           (10)

For i=j or k the first mixed term vanishes, because that intervention
removes one of the changed prescribed laws. Thus the two owned portions
are exactly −θ_i Δ_jΔ_k U_i. The untouched portions retain BOTH their
mixed prescribed and mixed deviation laws. There is no identification of
these coefficients with the original source reward gradient.

NOETHER's outer normal concerns an average of original-source vectors
Σλ[P_(μ[i←t])−P_μ]. Equation (10) is a DIFFERENT, two-law-difference
vector. The current normal and its selected scalar singleton-pressure
condition do not give its sign. A feasible raw reward direction relating
that original normal account to (10), with the same source weights and
the table's actual boundary faces, remains unproved. No individual
source reward gradient is silently declared a cube normal.

The endpoint-selection question has an already established obstruction
STRONGER than merely failing to price (10). HILBERT's
[all-player-tie theorem](CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md),
Section 5, says that every globally minimizing full semantic pair has
all four debts equal to m when the unrestricted minimum m is positive.
Its proof uses the checked singleton-margin theorem and a slack-aware
literal solo prefix; I reread that complete proof here.

Consequently there cannot be actual pair-repaired profiles ρ_n with
ε_n→0 and E_r(ρ_n)→m. Otherwise choose a convergent semantic subsequence:
its limit is globally minimizing, but has d_j=d_k=0, contradicting that
theorem. There is even a positive separation from m for sufficiently
small pair error; otherwise such a sequence could be selected. Pair
labels may be stabilized along a subsequence. For NOETHER's varying
r_n→r*, uniform reward Lipschitz bounds transport the same contradiction
to the fixed worst table r*. No strategy limit or actual attainment is
inferred.

This is a source-derived compulsory cost, not a counterexample to a
source-to-near-minimum pair theorem: proving that additional selection
theorem under the same positive-minimum hypothesis would itself contradict
the hypothesis and solve the problem. The unconditional pair producer
alone does not prove that comparison. Intermediate points of (4), before
both owner debts have been driven to zero, give a less restrictive next
construction, with every unrestricted tester still retained. No
orientation of that intermediate two-law move is proved. The pair
construction is not asserted to be an exhaustive architecture for uniform
equilibrium, and this observation is not proposed for a no-go gate.

## 5a. The complete intermediate mixture, with pair endpoints as probes

Keep the original source, its SAME certificate (3), and ANY actual
ρ∈Q_J(μ,ε). Let p_t mix BOTH changed marginal laws by t∈[0,1]. Define

    h_i=U_i(ρ)−U_i(p^10)−U_i(p^01)+U_i(μ).

For each repaired owner i∈J and EVERY response q, including after-support
dates and Never, the deviation payoff deletes one changed marginal.
Consequently its mixed difference is zero and

    C_(i,q)=−h_i.                                    (11)

This is stronger than merely knowing that the marked endpoint reply has
been repaired: it collapses the mixed coefficients of that owner's ENTIRE
response family to one prescribed-payoff scalar. In particular

    g_(i,q)(p_t)=(1−t)g_(i,q)(μ)+t g_(i,q)(ρ)
                                      +t(1−t)h_i.   (12)

Let χ_i(t) be the cap interpolation deficit

    χ_i(t)=(1−t)B_i(μ)+t B_i(ρ)−B_i(p_t)≥0.

The inequality follows because B_i(p_t) is a supremum of affine functions
of the OTHER changed marginal. The complete owned-debt identity is

    d_i(p_t)=(1−t)d_i(μ)+t d_i(ρ)
                         +t(1−t)h_i−χ_i(t),
    d_i(p_t)≤(1−t)e+tε+t(1−t)h_i.                   (13)

No ordinary convexity of the four-player maximum is used. If, for a
particular endpoint, h_j,h_k≤e−ε, both owned debts are at most
e−t²(e−ε). This is only a check on that endpoint, not a sign supplied by
pair Nash existence or by (3).

For each of the two untouched owners l, every complete tester remains:

    g_(l,q)(p_t)=(1−t)g_(l,q)(μ)+t g_(l,q)(ρ)
                                    −t(1−t)C_(l,q). (14)

The actual full objective is the maximum of the TWO owned expressions
in (13), with the χ terms retained, and ALL untouched rows (14). The
common tester pool is T_L, not the original T_N. Thus a newly exposed
deadline cannot disappear in this computation.

Here is the nonlocal crossing test at the SAME original source. Write
Δ_a=g_a(ρ)−g_a(μ) and ξ_a=e−g_a(μ)≥0. For t>0,

    g_a(p_t)<e−δ
      iff t[Δ_a−(1−t)C_a]<ξ_a−δ.                   (15)

All these inequalities must hold at one common t. For a source-active
untouched tester with endpoint leakage Δ_a>0 and 0<t<1, (15) with δ=0
requires C_a>Δ_a/(1−t)>0. At t=1 that tester already exceeds e. A
repaired owner's coefficient is instead −h_i; its
common quadratic can initially increase even though all its endpoint
responses are solved. Therefore neither endpoint repair nor a favorable
weighted mixed average gives a common crossing interval. Source-inactive
rows retain their actual ξ_a and cannot be omitted for a macroscopic t.

The same multiplier gives an additional necessary restriction without
introducing a new dual. Put D_λ=Σλ(A+B). The exact weighted gain at p_t is

    G_λ(p_t)=G_λ(μ)+tD_λ+t²C_λ,
    E(p_t)≥e−a₀−t b₀+t²C_λ.                         (16)

In particular, for δ>0, E(p_t)≤e−δ entails

    tD_λ+t²C_λ≤a₀−δ.

For an exact active KKT certificate this requires C_λ<0 and
t≥(D_λ+δ/t)/(−C_λ). It remains a NECESSARY weighted restriction;
every row in (15) must still be controlled. Equations (11)–(16) use the
original λ, not multipliers independently selected at p_t or ρ.

This calculation gives no full-objective sign under the positive global
minimum hypothesis. Its precise unconsumed quantities are the two scalars
h_j,h_k and the untouched tester-specific C_(l,q), together with their
actual source gaps ξ_(l,q). The current coupled reward normal and scalar
singleton-pressure bound do not price these mixed accounts. The common
owner-edge averaging test in NOETHER's collision-pair note likewise gives
no such sign. Calling the remaining contradiction impossible would be
incorrect: proving (15) simultaneously from the global-source hypotheses
would contradict the positive minimum, which is the intended use.

The optional payoff-fiber correction suggested in LARCH's survey was also
checked at this exact interface. It requires a feasible positive-support
block with a uniformly bounded payoff right inverse. Neither (1)–(3) nor
the reviewed coupled source theorem supplies that block or its bound.
Moreover correcting a prescribed payoff drift alone leaves both untouched
response envelopes in (14). No generic-rank assumption, unproved correction,
or cap-preserving consequence of payoff-only compression is imported.

The viable next use of the pair producer is consequently as a probe inside
a larger actual-law comparison that prices (14), not a claim that its
endpoints or independent intermediate mixtures are already a UE producer.
No separate export or no-go gate is proposed for this calculation.

## 6. Narrow source audit and arithmetic checks

Read named declarations under their imports, without a Lean edit or build:

- `QuittingTwoPlayerExistence.quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`
  in `UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean`.
  Its approximate pair-repair branch is essential; an exact stationary
  two-player Nash theorem is not asserted.
- `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`
  and `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`, for the equivalent
  finite 2×2 backward head construction.
- The finite-source route names `exists_minimum_quittingControllerFiniteWordLoss`,
  `antitone_quittingControllerFiniteWordValue`, and
  `tendsto_quittingControllerFiniteWordValue` in
  `UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`.

Prior-square comparison: NOETHER's
[two-law checkpoint](CODEX_NOETHER_SUPPORT__GLOBAL_KKT_TWO_LAW_COMPETITOR_CHECKPOINT.md)
already expands the full gain square and kills two marked replies; another
reply of either changed owner may still carry the gap there. RENY's
[simultaneous-response boundary](CODEX_RENY__SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY.md)
already retains all first-order rows and the full independent recombination
box. Neither inspected note constructs simultaneous full re-equilibration
of the two selected owners with frozen original outsiders. The new bounded
field is (1) feeding (5), with the explicit necessary mixed account (9).
QUANTILE's common-clock recombination theorem represents a supplied box but
does not produce (1) or orient (10).

Source notes used are FRECHET's
[enlarged-calendar comparison](CODEX_FRECHET_CYCLE__ENLARGED_CALENDAR_NEAR_OPTIMALITY_AND_CROSS_AMPLIFICATION.md)
and [silent-prefix certificate](CODEX_FRECHET_CYCLE__SILENT_PREFIX_ALL_OWNER_MULTIPLIERS.md),
and NOETHER's
[coupled worst-reward certificate](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md).
Their ordinary-mathematics status is retained; none is called a new checked
declaration here. The source information boundary in `arch/SUFFICIENT_STATE.md`
is respected by keeping actual original and changed marginal laws.

Exact rational arithmetic tested 180 frozen-outsider pair repairs over
30 signed integer tables, all six pairs, and two-date third-grid source
laws. In these arithmetic checks the induced pair tail was all Never
(the own singletons were nonpositive), and backward 2×2 Nash roots were
computed exactly. Both changed complete debts were zero, both outsider
laws stayed unchanged, and every full gain obeyed (4), including the
after-support and Never rows. These are checks of the adapter and algebra,
not claimed positive-global-minimum examples.

The intermediate identities (11)–(14) were additionally checked in 864
exact rational owner-level cases: twelve signed integer reward tables,
all six changed pairs, and t∈{1/4,1/2,3/4}, using independent three-action
source/target laws. The complete after-support and Never responses were
retained. These checks verify the identities, cap interpolation deficits,
and full envelopes; those arbitrary profiles are not substituted for a
globally minimizing source or used as a counterexample to its hypotheses.

For the final source comparison I also read the whole ordinary-math
[silent-source coupling bridge](CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE.md)
and independently accepted its frozen source in
[owned feedback](../feedback/CODEX_FRECHET_CYCLE__SILENT_SOURCE_COUPLING_TO_WORST_REWARD_PRESSURE__BY_CODEX_TARSKI_PREMIUM.md).
Its same NEW weights, all-owner mass, and scalar pressure do not by
themselves add a mixed-account sign. NOETHER's complete
[collision-pair averaging test](CODEX_NOETHER_SUPPORT__COLLISION_PAIR_AVERAGING_WRONG_SIGN.md)
was read for that exact sign question, and Section 5 of
[LARCH's survey](CODEX_LARCH__MISSING_THEORY_SURVEY.md)
was read for the proposed payoff correction. Neither is asserted to
contain the missing joint full-cap comparison.
