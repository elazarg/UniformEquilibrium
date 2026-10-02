# R: payoff-preserving repair with one survival-weighted abnormality term

Recorder and independent checker: `CODEX_FRECHET_CYCLE`.

Status: ordinary mathematics reconstructed from the THIRD response in
`gpt/R.md`, input SHA
`bc35abd855ba89f228c50079d08524d44b8964d8e893257e71062c7c6fe66593`.
The complete intake review is `feedback/R__BY_CODEX_FRECHET_CYCLE.md`.
This is preservation of user-supplied mathematics, not a claim of independent
discovery or a new general equilibrium-existence theorem. No Lean or export.

The specific refinement is simultaneous: original source payoff changes
by at most ε; every nonexceptional player's full debt is O(ε log(1/ε));
one exceptional player's debt is O(√ε) plus its abnormality multiplied by
the actual opponents' prefix survival. The √ε exponent is necessary under
O(ε) source-payoff preservation.

## 1. Data and statement

Let I be a finite nonempty player set. Quitting rewards are r(S), Never
pays z, players' complete stopping laws are independent, and unilateral
replacements are unrestricted behavioral laws. Choose M>0 such that
|r_i(S)−z_i|≤M. Define own singletons s_i, exact punishment infima P_i,
full caps B_i, and debts d_i=B_i−U_i. Put

    A_i=(P_i−s_i)₊.

Let x=(q_t) be an ACTUAL initially absorbing behavioral root sequence.
At EVERY date its root is playerwise ε-perfect against its actual
restarted tail, including at histories of zero prescribed reach. Here
0<ε<2M. In particular both pure endpoint payoffs are at most the prescribed
root payoff plus ε, and every positively supported endpoint is at least
the prescribed payoff minus ε. No punishment normality is assumed.

Set

    θ=ε/(2M),
    S_i(t)=∏_(k<t)(1−q_k^i),
    b_i(t)=∏_(j≠i)S_j(t).

Let K be the first positive integer with some S_i(K)≤θ, choose ANY such
i=i*, and put β=b_i(K). Then there is a finite T≥K and an actual profile
σ agreeing with x at all dates before T such that

    |U(σ)−U(x)|∞≤ε,
    d_j(σ)≤2ε log(2M/ε)+3ε                       (j≠i*),
    d_i*(σ)≤β A_i*+2√(2Mε)+2ε log(2M/ε)+4ε.    (REPAIR)

The replacement after T is one fixed independent punishment tail for i*,
or all Continue. There is no public random choice of tail, simultaneous
attainment of P coordinates, or strategic minimum-attainment assumption.

## 2. Proof

Subtract z from every terminal and Never payoff. Every payoff and every
deviation payoff shifts by the same coordinate constant. Row perfection,
debts, A_i, and payoff differences are unchanged. Hence assume z=0 and
all rewards have absolute value at most M. Every actual tail payoff is
then in [−M,M]ⁱ, including null-history restarts.

For a fixed player j let L_j(t) be the expected absorbing payoff earned
strictly before t when j always Continues and opponents follow x. Let
γ_t^j be the actual source payoff from restart t. Define

    W_j(t)=L_j(t)+b_j(t)γ_t^j.

This is the actual payoff from Continue through dates strictly below t and
then resume the prescribed conditional law. Independence identifies the
opponents' survival as b_j(t), even if j's own prescribed survival is zero.
The exact Bellman recursion gives

    W_j(t+1)−W_j(t)=b_j(t)(C_t^j−γ_t^j).       (LEDGER)

Playerwise row perfection implies

    C_t^j−γ_t^j≤ε,
    C_t^j−γ_t^j≤2ε q_t^j.                    (ROW)

For the second inequality, q_t^j=0 gives equality zero. Otherwise the
supported-Quit lower inequality and Continue upper inequality give
C_t^j−Q_t^j≤2ε; multiply by q_t^j using the prescribed root mixture.
The full pure response Quit at date t has value

    F_j(t)=L_j(t)+b_j(t)Q_t^j≤W_j(t)+ε.       (QUIT)

### First crossing and the nonexceptional clocks

Initial absorption means ∏_j S_j(t)→0. Since I is finite and the
individual survivals decrease, some S_j(t) tends to zero. Thus K exists.
Minimality gives S_j(K−1)>θ for EVERY player. Consequently

    Σ_(t<K−1) q_t^j ≤ Σ_(t<K−1) −log(1−q_t^j)
                      =−log S_j(K−1)<log(1/θ).

All factors here are positive. A possible sure Quit on the last crossing
row is excluded from this logarithmic sum and handled using the first
bound in (ROW). Applying (LEDGER) yields, simultaneously for every j and
0≤t≤K,

    W_j(t)≤U_j(x)+Λ,
    Λ=2ε log(1/θ)+ε.                          (PREFIX)

Moreover, joint prescribed survival at K is at most θ. If j≠i*, its
opponents include i*, so b_j(K)≤S_i*(K)≤θ. These inequalities remain
true at all later cutoffs.

### The exceptional scan

Write i=i*. Put

    h=ε+√(2Mε),       c=(h−ε)/(2M)=√(ε/(2M))∈(0,1).

Starting at K, take the first T for which either

    γ_T^i≥P_i−A_i−h,                         (GOOD)
    b_i(T)≤θ.                               (CLEAR)

At a date before this stopping time, (GOOD) fails. Since
P_i−A_i=min(P_i,s_i)≤s_i, the Quit upper bound gives

    Q_t^i≤γ_t^i+ε<s_i−(h−ε).

If H_i(t)=1−∏_(j≠i)(1−q_t^j) is current opponent absorption, then
Q_t^i≥s_i−2M H_i(t): if no opponent Quits the payoff is s_i, and the
remaining payoff differs by at most 2M. Hence H_i(t)>c. Before stopping,
b_i therefore decays by factors strictly below 1−c. This proves T is
finite and also gives the stronger duration-free estimate

    Σ_(t=K)^(T−1) b_i(t)≤β/c.

Using the first inequality in (ROW), rather than multiplying ε by the
number of scanned rows, shows for K≤t≤T that

    W_i(t)≤U_i(x)+Λ+εβ/c
          ≤U_i(x)+Λ+√(2Mε).                  (SCAN)

### One actual tail and all complete responses

If (GOOD) holds, choose opponents independently with full cap for i at
most P_i+ε, which exists by the definition of the infimum. Complete
their laws to a full tail arbitrarily and append that ONE tail at T.
The cap of every response that Continues up to T is at most

    L_i(T)+b_i(T)(P_i+ε)
      ≤W_i(T)+b_i(T)(A_i+h+ε)
      ≤W_i(T)+β A_i+h+ε.                      (TAIL)

If only (CLEAR) is used, append all Continue. Every conditional deviation
payoff is at most M and γ_T^i≥−M, so the analogous bound is

    L_i(T)+b_i(T)M≤W_i(T)+2Mθ=W_i(T)+ε.

For a deviation Quitting before T, opponents have not been altered before
its terminal event; use (QUIT), (PREFIX), and (SCAN). Responses at T,
all later finite dates, and Never are bounded by the appended tail's
complete cap. Every behavioral replacement is an independent stopping-time
law, whose payoff is the average of the pure finite-date and Never values.
Thus these comparisons bound ALL unrestricted deviations.

The profiles agree before T, and their prescribed conditional payoffs are
bounded by M. Their original payoff difference is therefore at most
2M times joint prescribed survival to T, which is ≤2Mθ=ε.
Subtracting the repaired payoff from (SCAN) and (TAIL) gives

    d_i(σ)≤β A_i+2√(2Mε)+2ε log(2M/ε)+4ε.

For j≠i, responses Quitting before K use (QUIT) and (PREFIX). Every
response reaching K has payoff at most

    L_j(K)+b_j(K)M≤W_j(K)+2Mθ≤U_j(x)+Λ+ε,

regardless of the intervening scan or chosen tail. Subtracting the repaired
payoff gives Λ+2ε=2ε log(2M/ε)+3ε. This proves (REPAIR).

If both stopping conditions hold, the punishment branch is legitimate and
already gives the asserted bounds. Zero prefix reach and sure crossing
rows cause no division by zero in the proof.

## 3. A quantitative source consequence under a global gap

Suppose E(p)=max_j d_j(p)≥g>0 for EVERY actual product-law profile.
Define f_M(ε)=2√(2Mε)+2ε log(2M/ε)+4ε. If f_M(ε)<g, applying
(REPAIR) gives

    β A_i*≥g−f_M(ε)>0.

Thus the selected player is abnormal, and

    β≥(g−f_M(ε))/(P_i*−s_i*).

The event that i* stops before K and all opponents survive to K has
probability (1−S_i*(K))β. On that event the terminal coalition of the
ORIGINAL SOURCE is exactly {i*}. Therefore its singleton terminal atom is
at least

    (1−θ)(g−f_M(ε))/(P_i*−s_i*).

This is an actual terminal-law consequence, not a calendar atom claim or
a claim that a cap-carrier point is realized. It leaves precisely the
displayed abnormality term; it does not refute a positive-gap game.

## 4. Sharp exponent for payoff-preserving repair

Take two players, Never zero, both singleton reward vectors (0,0), and
joint reward (−1,0). Both players are normal with P=s=0. At the fully
mixed stationary source q=(1/2,h), 0<h<1, exact calculation gives

    U₁=−h/(1+h),  Q₁=−h,  C₁=−h(1−h)/(1+h),
    U₁−Q₁=C₁−U₁=ε_h=h²/(1+h).

Player 2 is indifferent everywhere, so these are playerwise ε_h-perfect
actual rows. Joint Continue is (1−h)/2<1/2, and opponents' survival after
deleting either player tends geometrically to zero. Every finite live
history has positive probability.

Player 1 guarantees zero by Never against ANY opponents and can never
receive a positive payoff. Consequently d₁(p)=−U₁(p) for EVERY actual
profile, and a repair satisfying |U(p)−U(x^h)|∞≤ε_h must have

    E(p)≥h/(1+h)−ε_h=h(1−h)/(1+h).

Its ratio to √ε_h tends to one. More generally replacing the payoff
accuracy by Cε_h for any fixed C leaves the same asymptotic ratio. Thus
o(√ε) regret cannot be guaranteed with O(ε) source-payoff preservation.
This does not exclude faster equilibrium production without that payoff
constraint: all Continue is an exact equilibrium of this very table.

## 5. Novelty boundary and sources

Already checked: the first-survival switch/ledger mechanism and the
normal-source existence compiler. In
`UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`,
`exists_normalSupportDelayedSwitch` uses a finite scan, while
`quittingLedger_add_le_of_supportApproxNash` charges its extra rows by
their count. `exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing`
and its uniform-payoff wrapper already consume all-normal S.3.

Also already checked:
`exists_isεAsymptoticNash_of_completelyAbsorbing_supportRationalPath`
in `Quitting/Paths/SupportWitnessPathCompiler.lean` gives
2δ+r+√δ(2+7·quittingRewardBound) once all-date rationality is supplied.
The reviewed ordinary floor-amplification lemma in
`CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md`
gives O(√ε) floors on normal row-perfect actual spines. Thus neither the
existence conclusion nor a square-root bound in isolation is new.

The retained refinement is the full (REPAIR) package with ε payoff change,
the exceptional survival-weighted abnormality, and the stronger individual
nonexceptional bounds, together with its specifically payoff-preserving
lower bound. A narrow source/note search found no existing version of this
combined result. The old square-root support-rational compiler is not being
relabelled as new mathematics.

The input's universal hardness equivalence and four-player reverse-S.3
corollary are recorded in the review at their existing production homes.
They are not republished here. No new research is begun from the remaining
abnormality term. Requested next check: independent whole-proof review of
this preserved quantitative refinement if the coordinator wishes to gate it.
