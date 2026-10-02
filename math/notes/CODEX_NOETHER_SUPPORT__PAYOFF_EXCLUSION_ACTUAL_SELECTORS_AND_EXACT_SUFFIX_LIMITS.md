# Payoff exclusion, actual finite selectors, and exact suffix limits

Authors: the supplied GPT contributors; CODEX_NOETHER_SUPPORT (independent
consolidation). The two-pair input is credited for its independent-clock
entrance.

Independent review: [CODEX_FRECHET_CYCLE](../feedback/CODEX_NOETHER_SUPPORT__PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS__BY_CODEX_FRECHET_CYCLE.md).

Independent source audits by CODEX_NOETHER_SUPPORT, completed before this
consolidation: [auxiliary and exact limits](../feedback/AUXILIARY_CAP_DESCENT_AND_EXACT_LIMITS__BY_CODEX_NOETHER_SUPPORT.md),
[weak exclusion and determinant](../feedback/WEAK_SINGLETON_PAYOFF_EXCLUSION_AND_DETERMINANT_SELECTOR__BY_CODEX_NOETHER_SUPPORT.md),
and [two-pair entrance only](../feedback/TWO_PAIR_PAYOFF_EXCLUSION_AND_GEOMETRIC_FINITE_MENU_SELECTION__BY_CODEX_NOETHER_SUPPORT.md).

The outputs are actual finite laws with total complete-deviation control,
a finite raw-table entrance, and an exact every-suffix conclusion on the
strict subclass. Four-player qualitative weak-exclusion existence is already
implied by the existing strict-minimum theorem. The separate cap-threshold
argument provides different arbitrary-source descent and stronger minimum
margins; those margins are not repeated here.

## Exact question and model

Let I be finite and nonempty, n=|I|. Nonempty quitting coalition S pays the
vector r(S); infinite all-Continue pays zero. Fix M>0 with |r_i(S)|≤M and
write s_i=r_i({i}). Before absorption the only public history is the live
clock. Each player has independent private randomization. Thus a complete
behavior strategy is equivalent to one law on ℕ∪{Never}. A unilateral
deviator may replace that entire law; all finite dates, unbounded support,
and Never are allowed. No public signal or correlated lottery is supplied.

For an actual product p of stopping laws define

    U_i(p) = prescribed expected terminal reward,
    B_i(p) = sup over all replacement laws of the deviator's terminal reward,
    d_i(p) = B_i(p)-U_i(p),       D(p)=Σ_i d_i(p).

The cap is the supremum of pure finite-date and Never response values,
because every replacement payoff is their probability-weighted average.
In particular −M≤U_i,B_i≤M and d_i≥0. No cap attainment is assumed.

A finite word has N product rows, then all-Never. We seek actual such words
with D<ε, not merely Nash equilibria against a finite response menu. We also
ask when one infinite row sequence is exact terminal Nash at every suffix.

The following are the hypotheses used separately below.

1. Strict deficit (PD): some κ>0 satisfies, for every finite word p,
   min_i(U_i(p)−s_i)≤−κ.
2. Nonconcentrated group exclusion (GE): there is β<1 and a collection of
   probability weights w with max_i w_i≤β such that every finite word p
   admits a weight with Σ_i w_i(U_i(p)−s_i)≤0.
3. Weak subset exclusion (WE): there is a nonempty J⊆I with s_i≥0 for i∈J
   such that every finite word p has U_i(p)≤s_i for some i∈J.

Other singleton signs are unrestricted under each finite-law theorem except
for the stated signs on J. Under (PD), nonnegative singletons for every
player additionally yield one exact every-suffix terminal equilibrium.

## A common literal-prefix calculation

For q∈[0,1]^I put c=∏_i(1−q_i), a=1−c,
β_i=∏_{j≠i}(1−q_j), and π_i=q_iβ_i. Let Q_i(q) be Quit-now reward, and
let H_i(q) be the absorbing contribution when i Continues. The Continue
endpoint annotated by v_i is H_i+β_i v_i. Prefixing q to an actual old word
has exactly

    U'_i=q_i Q_i+(1−q_i)(H_i+β_i U_i),
    B'_i=max(Q_i,H_i+β_i B_i).                           (1)

The latter identity follows by splitting a complete response into Quit now
and Continue now followed by an arbitrary old response. Suprema commute with
the nonnegative coefficient β_i, including β_i=0. The all-Never seed has
U_i=0 and B_i=max(s_i,0). Thus (1) computes complete caps for every finite
word. Equivalently one can scan its N dates, one finite date after its final
row, and Never: all further finite dates are outcome-equivalent.

For h≥0 let v=B−h·1, and let g_i be ordinary mixed-action regret at q in
the finite Boolean game with continuation v. If w_i is its mixed payoff,

    B'_i≤w_i+g_i+β_i h,       U'_i=w_i+c(h−d_i).

Since β_i−c=π_i, summing the differences gives

    d'_i≤c d_i+π_i h+g_i,
    D'≤D−a(D−h)+Σ_i g_i.                               (2)

Here Σ_iπ_i≤a; simultaneous quitting improves the bound. Individual debts
can increase. This is a bound on the complete caps after the actual prefix,
not on caps of the annotation v.

If v_i≤s_i−δ for some δ>0, conditioning on opponent absorption gives

    Q_i−H_i−β_i v_i≥β_iδ−2M(1−β_i)
                        ≥δ−(2M+δ)a.                    (3)

No bound on v is required. An exact Nash root therefore has a≥δ/(2M+δ):
otherwise Quit is strictly better for i, so q_i=1, contradicting the bound
on a. If every g_i≤δ/4, instead a≥δ/[2(2M+δ)]. Indeed, below this latter
bound q_i≤a<1/2 and the Quit advantage exceeds δ/2, so g_i>δ/4.

The exact-root part of (2) is an existing repository theorem. Its use as a
literal iterative producer and its explicit approximate-root error budget
are the relevant assembly here.

For rational data and a positive rational tolerance η, an η-regret root can
be selected by exhaustive rational grid search. If all pure Boolean-game
payoffs are bounded by R>0, coupling the n independent action draws shows
that a mixed payoff changes by at most 2Rn‖q−q'‖∞. Each pure-action endpoint
has the same bound, so ordinary regret is 4Rn-Lipschitz. Finite-game Nash
existence and a rational grid of mesh at most η/(4Rn) ensure acceptance.
All acceptance inequalities are rational calculations. This proves
termination, without a polynomial-time or bit-complexity assertion.
For these algorithms the reward bound M, the target error, and supplied
quantitative bounds κ or β are taken rational. Real valid bounds can be
weakened to rational ones: increase M or β while keeping β<1, and decrease
κ while keeping κ>0. The construction assumes its stated exclusion
condition; it does not recognize that condition for arbitrary raw tables.

## Strict-deficit finite selection and exact limits

Under (PD), start at all-Never and at stage m set

    D₀=Σ_i max(s_i,0),    t_m=min(D_m,κ/2),
    h_m=D_m−t_m,         v^m=B^m−h_m·1,
    A=κ/(4M+κ).

The all-Never test implies D₀≥κ. If U_i^m≤s_i−κ, then

    v_i^m=U_i^m+d_i^m−D_m+t_m≤s_i−κ/2.

Choose any exact Nash root q^m against v^m and prepend it to the entire old
word, obtaining p^{m+1}=q^m::p^m. Equations (2)–(3) give

    a(q^m)≥A,       D_{m+1}≤D_m−A min(D_m,κ/2),
    D_N≤D₀[1−κ²/(2D₀(4M+κ))]^N.                        (4)

The last step uses D_m≤D₀ and
min(D_m,κ/2)≥κD_m/(2D₀). If D_m=0, choosing exact Nash roots against
v^m=B^m=U^m continues the sequence with zero debt and the same absorption
floor. For rational data, choose max_i g_i≤A t_m/(4n) whenever D_m>0.
This is at most κ/8, so a≥A/2, and

    D_{m+1}≤D_m−(A/4)min(D_m,κ/2),
    D_N≤D₀[1−κ²/(8D₀(4M+κ))]^N.                        (5)

The rational finite construction stops upon reaching its requested error.
The exact construction is allowed to continue indefinitely.

Assume now all s_i≥0. The chronological rows of p^N are
q^{N−1},q^{N−2},…,q^0. Compactness and diagonal extraction give an increasing
N_k and rows q̄_t such that q^{N_k−1−t}→q̄_t for every fixed t. Each limit
row has absorption at least A. Every suffix consequently survives L rows
with probability at most (1−A)^L. Finite-prefix payoff convergence and a
remainder bounded by M(1−A)^L imply

    U(p^{N_k−t})→U(q̄^t)                               (6)

for every fixed t; q̄^t denotes the literal suffix starting at row t. The
approximating suffix is exactly p^{N_k−t}. No unrelated suffix selection or
assumption of cap continuity enters (6).

A fixed pure response date ℓ depends on finitely many opponent rows. Pass
its bound by U_i(p^{N_k−t})+D_{N_k−t} to the limit using (4) and (6).
Every finite response date is therefore bounded by U_i(q̄^t).

For arbitrary fixed opponent laws, let O_i be their first quit date, with
O_i=Never if none quits. The late finite-response values satisfy

    lim_{ℓ→∞} U_i(Quit at ℓ,opponents)
      =U_i(Never,opponents)+s_i Pr(O_i=Never).          (7)

For each realization with O_i finite, sufficiently late own quitting leaves
the opponent coalition unchanged; for O_i=Never it pays s_i. Bounded
convergence proves (7). Since s_i≥0, Never is no better than this limit.
Taking averages over complete replacement laws now proves exact terminal
Nash at every suffix, including suffixes not reached from the initial row.
Prescribed joint absorption does not imply opponent-deleted absorption;
equation (7) handles precisely that missing implication.

This same infinite profile is uniform at its initial terminal payoff. With

    e_{H,i}=E[1_{O_i finite} min((O_i+1)/H,1)],

bounded convergence gives e_{H,i}→0. On an own-only quit, a nonnegative s_i
cannot gain from finite-average truncation. Every other negative terminal
reward occurs at the finite opponent clock O_i. Therefore, uniformly over
complete responses, average payoff is at most B_i+M e_{H,i}. Prescribed
average payoff differs from U_i by at most M/(AH), because expected
absorption date plus one is at most 1/A. The regret bound is
M e_{H,i}+M/(AH)→0. No rate for the opponent-deleted clock is asserted.

## Nonconcentrated group selection

Under (GE) put ρ=1−β>0. At a positive-debt source choose
t=ρD/2, h=D−t, v=B−h·1. A witnessing weight satisfies

    Σ_i w_i(v_i−s_i)≤βD−h=−t.

Some coordinate is below its singleton by at least t. Exact roots give

    D'≤D−ρ²D²/(8M+2ρD).                               (8)

Set C=[8M+(2ρ−ρ²)D₀]/ρ². If D'>0, (8) yields
1/D'−1/D≥1/C, hence

    D_N≤CD₀/(C+ND₀).                                  (9)

For rational roots choose max_i g_i≤t²/[4n(2M+t)]. This is at most t/4.
The absorption floor is halved, and the aggregate error consumes half that
gain, giving D'≤D−ρ²D²/(32M+8ρD). Formula (9) holds with
C=[32M+(8ρ−ρ²)D₀]/ρ². Zero debt terminates either construction. Signs of
the individual singleton rewards do not enter this theorem. Unlike (PD),
(GE) does not produce a fixed positive absorption floor.

Here is the complete raw two-pair entrance credited to the supplied
two-pair manuscript. For four players let A₀={0,1}, B₀={2,3}, and define
G_A(u)=((u₀−s₀)+(u₁−s₁))/2 and G_B analogously. Assume s₀+s₁≥0,
s₂+s₃≥0, and numbers a,b,L≥0 with a≤b+2L such that

    (G_A(r(A₀)),G_B(r(A₀)))≤(a,−b),
    (G_A(r(B₀)),G_B(r(B₀)))≤(−b,a),
    (G_A(r(S)),G_B(r(S)))≤(−L,−L) for all other S.       (10)

For arbitrary independent clocks let x,y,ν be the probabilities of A₀,B₀,
and Never, and z=1−x−y−ν. For pair (T₀,T₂) put
α₁=Pr(T₀<T₂), β₁=Pr(T₂<T₀), γ₁=Pr(T₀=T₂=Never);
define α₂,β₂,γ₂ similarly for (T₁,T₃). Each triple sums to at most one,
and the two pairs are independent. Thus x≤α₁α₂, y≤β₁β₂, ν=γ₁γ₂.
Cauchy–Schwarz gives √x+√y+√ν≤1, hence z≥2√(xy).

Using (10), if x≤y then

    G_A(U)≤ax−by−Lz−ν(s₀+s₁)/2
           ≤(a−b−2L)x−b(y−x)≤0.

For y≤x use G_B. This proves (GE) with the two uniform pair weights,
β=1/2. The exact and rational constants in (9) are respectively
32M+3D₀ and 128M+15D₀. This quantitative complete-debt producer does not
require the additional singleton joining-gain hypotheses in the older
finite-menu Nash construction.

## Weak-subset finite selection

Assume (WE). Start with all-Never, D₀=Σ_i max(s_i,0). Zero debt is terminal.
At a working tolerance 0<e≤M, repeat while D≥e, using

    τ=e/8,  θ=e/(16M),  A_e=τ/(4M+τ),
    η=A_eτ/(8n),       Δ=A_eτ/8.                        (11)

All numbers are rational when the input and e are rational.

If min_i(B_i−s_i)≤D−τ, set h=D−τ/2≥0 and select a rational root with every
regret at most η against B−h·1. A coordinate is below its singleton by τ/2.
Since η≤τ/8, (3) gives a≥A_e/2, and (2) yields

    D'≤D−aτ/2+nη≤D−Δ.                                 (12)

Call this a charged step. Recompute the actual complete caps after every
prefix. Throughout the algorithm D≤D₀, so R=M+D₀ is a valid grid bound.

Otherwise B_i−s_i>D−τ for every i. Choose a witnessing i∈J with U_i≤s_i.
Nonnegative debts imply

    d_i>D−τ,        Σ_{j≠i}d_j<τ,       s_i−τ<U_i≤s_i,
    U_j>s_j+D−2τ≥s_j+3e/4  (j≠i),      B_i>s_i.        (13)

Test the finite singleton column. If every outsider satisfies
r_j({i})≥s_j+e/4, the stationary profile in which only i quits with hazard
θ is exact terminal Nash. Indeed, owner i's prescribed payoff and cap are
s_i≥0. For outsider j, put v_j=r_j({i}) and
Q_j=(1−θ)s_j+θr_j({i,j}). Then

    v_j−Q_j≥(1−θ)e/4−2Mθ>0.

Quit at date k pays [1−(1−θ)^k]v_j+(1−θ)^kQ_j≤v_j;
Never pays v_j because the owner quits almost surely. This bounds every
complete replacement. To obtain finite laws, truncate the solo clock after
K rows and send its remaining mass to Never. Put z=(1−θ)^K. Its prescribed
payoff is (1−z)r({i}). Owner regret is zs_i. An outsider's pre-cutoff
response is unchanged and ≤v_j; any late finite response pays
(1−z)v_j+zs_j≤v_j; Never pays (1−z)v_j. Thus its cap is at most
max(v_j,(1−z)v_j), and its regret is ≤z max(v_j,0), even when v_j<0.
Consequently D≤nMz. Take K>θ⁻¹log(nM/ε) for the original target ε.

If the column test fails, prepend solo-i rows with hazard θ until D<e or
some outsider has U_j≤s_j+e/2. Before each row every outsider has
Continue-minus-Quit at least (1−θ)e/2−2Mθ>0, evaluated at the actual U.
Since B_j≥U_j, its Continue cap branch also wins. The owner cap remains
B_i>s_i. Exact subtraction in (1) therefore gives

    U'_i=θs_i+(1−θ)U_i,       B'_i=B_i,
    U'_j=θr_j({i})+(1−θ)U_j, d'_j=(1−θ)d_j (j≠i),
    D'=D−θ[(s_i−U_i)+Σ_{j≠i}d_j]≤D.                    (14)

The owner's root mixture need not be optimal. Its payoff increases towards
s_i, so the nonnegative bracket in (14) persists throughout the block.

Some outsider has r_j({i})<s_j+e/4. After k rows its payoff is
r_j({i})+(1−θ)^k(U_j−r_j({i})). Since |U_j−r_j({i})|≤2M, the block
stops within

    L(e)=ceil[(16M/e) log(8M/e)]                        (15)

rows. At a threshold crossing with D≥e, the outsider debts still total
less than τ, so the crossing player has
B_j−s_j≤e/2+τ=5e/8<D−τ. The next step must therefore be charged.

Every block of at most L(e)+1 rows thus either terminates or spends Δ of
actual total debt. If a stage begins with debt D_in, a valid row bound is

    (L(e)+1)(ceil(D_in/Δ)+1),                           (16)

apart from the separately bounded stationary truncation. Hence every stage
terminates. First run e=M if D₀>M, costing O(n) rows. Then use dyadic
levels, each with D_in≤2e, until the last level e∈(ε/2,ε]. Since
Δ=e²/[512(4M+e/8)]≥e²/(2112M), summing (16) gives

    O(n+(M/ε)² log(16nM/ε))                            (17)

for 0<ε≤M, with an absolute constant. A stationary exit at an earlier
working level is truncated to the original ε; its θ is at least ε/(32M),
so that cost is absorbed in (17). A one-player positive-debt stage is also
covered: the outsider column test is vacuous and gives the solo exit.

## The separate-cross-mass determinant entrance

For four players put A₀={0,1}, B₀={2,3},
Z₊={{0},{3},{0,3}}, Z₋={{1},{2},{1,2}}. Write x,y,z₊,z₋ for the
terminal probabilities of A₀,B₀,Z₊,Z₋. The independent comparisons used
above, omitting γ, give

    x≤α₁α₂, y≤β₁β₂, z₊≥α₁β₂, z₋≥β₁α₂,
    xy≤z₊z₋.                                          (18)

For example T₀<T₂ and T₃<T₁ imply the first coalition is one of
{0},{3},{0,3}. Strict inequalities ensure the earlier clocks are finite,
even with Never present. Ties do not satisfy these comparisons. Thus (18)
has no hidden absorption or finite-support premise.

Assume s₀,s₁≥0, with other singleton signs arbitrary. Choose a,b,l,m>0
with ab≤lm, and impose on every nonempty coalition S

    r₀(S)−s₀≤a·1_{S=A₀}−l·1_{S∈Z₋},
    r₁(S)−s₁≤b·1_{S=B₀}−m·1_{S∈Z₊}.                  (19)

Never contributes −s₀,−s₁ to the two surpluses. Thus
U₀−s₀≤ax−lz₋ and U₁−s₁≤by−mz₊. If both were positive, multiplication
would give abxy>lmz₋z₊≥abxy, impossible. This proves (WE) for J={0,1}.
The thirty finite linear row tests and one product test therefore produce
the actual finite selectors above and one fixed uniform payoff.

The theorem attaches independent-clock information to complete reward-table
data; no caps, continuation labels, stationary equilibria, or selected
strategy sequence are inputs. It is a sufficient class, not an exhaustive
characterization of quitting games. Once (18)–(19) establish the exclusion,
the entire determinant class's qualitative Fin4 existence conclusion also
follows from the existing strict-minimum theorem. The attachment supplies an
explicit raw criterion and the quantitative actual selector above; it is
not a new general qualitative Fin4 existence mechanism.

## Uniform payoff delivery and the pivot consumer

For any fixed N-date word, prescribed H-stage average payoff differs from
terminal payoff by at most M(N+1)/H. Uniformly over a deviator, average
payoff is at most B_i+M(N+1)/H. If s_i≥0, truncating a late sole own quit
cannot improve its terminal contribution. If s_i<0, replace all own quitting
dates after the opponents' final finite date by Never; the new complete law
removes their nonpositive solo contribution. Earlier opponent outcomes stay
unchanged and their timing error is bounded by M(N+1)/H. This proves the
bound for pure responses and hence all mixtures. Finite-horizon regret is
at most D+2M(N+1)/H, with every sufficiently large horizon covered.

Select a convergent subsequence of the bounded prescribed terminal payoffs
of words with D→0. Its limit is one fixed target. For each ε select one
word whose debt and target distance are small, then one horizon threshold.
This supplies exactly the fixed-target uniform-equilibrium quantifier order.

In canonical Fin4, retain the three nonpivot laws from a constructed word.
The displayed pivot law is already a feasible competitor for the complete
regret minimization, so its optimal pivot-repair objective is ≤D. No claim
is made that an arbitrary pivot best response preserves outsider debts.

## Boundary tests and falsification attempts

The determinant is attained: let T₀,T₁ independently be date zero with
probability p and Never otherwise, and let T₂=T₃=1 surely. Then
x=p², y=(1−p)², z₊=z₋=p(1−p). This also attains √x+√y=1. All-Never
gives zero in (18), so Never does not require a separate positivity claim.

The complete determinant fixture below uses s=(1,0,0,0), M=21,
a=20, b=l=1, m=20. Every row satisfies (19) directly.

| S | r₀ | r₁ | r₂ | r₃ |
|---|---:|---:|---:|---:|
| {0} | 1 | −20 | 1 | 1 |
| {1} | 0 | 0 | 1 | 1 |
| {0,1} | 21 | 0 | 0 | 0 |
| {2} | 0 | 0 | 0 | 1001/1000 |
| {0,2} | 1 | 0 | 0 | 1 |
| {1,2} | 0 | 0 | 3 | −2 |
| {0,1,2} | 1 | −2 | 2 | 2 |
| {3} | 1 | −20 | 1 | 0 |
| {0,3} | 1 | −20 | 2 | 0 |
| {1,3} | 1 | 0 | −1 | 3 |
| {0,1,3} | 1 | 0 | −1 | 2 |
| {2,3} | 1 | 1 | 1 | 1 |
| {0,2,3} | 1 | 0 | −2 | 1 |
| {1,2,3} | 1 | 0 | 1 | 3 |
| {0,1,2,3} | 1 | 0 | 3 | −2 |

Pure B₀ has surplus (0,1,1,1), refuting (PD). For every probability
weight with max coordinate≤β<1 its surplus is 1−w₀≥1−β>0, refuting (GE)
even with profile-dependent weights. At that same root the only active
players 2 and 3 have Quit payoff 1>s₂=s₃. Thus the own-singleton endpoint
condition fails: that condition asks every absorbing product root to have
an active i with Q_i≤s_i. The half-A₀/half-B₀ correlated lottery has payoff
(11,1/2,1/2,1/2)>s, excluding every nonzero nonnegative linear separator
of the full reward convex hull. These separate named criteria only; they
do not say the fixture has no easy equilibrium. It does have an exact
one-row equilibrium q=(1,1/3,10/11,0), with payoff/caps
(53/33,−20/11,2/3,14/11).

For the weak algorithm, the supplied exact checker starts from rows
(0,1/200,0,0),(0,0,1,1). Direct scans give
U=(199/200,199/200,1,1), B=(11/10,1,1,200199/200000),
D=22199/200000. At e=1/10 the charged test fails, and owner 0 cannot take
the stationary column exit. Exactly 155 solo-0 prefixes of hazard 1/3360
produce the first outsider payoff crossing. They satisfy every complete-cap
identity in (14). Root q above then makes D=0. Independent forward response
scans agree with the backward caps over all 158 rows, the late date, and
Never. This is a regression of the block mechanism, not evidence of a
necessary long chronology.

The exact-limit sign hypothesis has a sharp counterexample. For 0<δ<1 let
two-player zero-sum rewards to player 0 be 1 at {0}, 1−δ at {1}, and −1
at {0,1}. Player 1 receives their negatives. Then s=(1,δ−1), and the
sum of coordinate surpluses is −δ, so (PD) holds with κ=δ/2. Nevertheless
there is no exact terminal Nash profile.

To prove this, player 1's constant hazard δ/2 makes every pure response of
player 0, including Never, pay V=1−δ. If player 0 uses constant hazard p>0,
every response of player 1 has payoff ≤−V+(2−δ)p, by conditioning on the
first player-0 quit. Sending p→0 fixes the zero-sum value at V. At a Nash
profile write p_t=Pr(T₀=t), S_t=Pr(T₀≥t), including Never. Player 1's
Quit-at-t payoff is −1+δS_t+(2−δ)p_t. Its bound by −1+δ forces p₀=0;
induction forces p_t=0 for every finite t. Thus player 0 plays Never, and
player 1 can also play Never for 0>−V, a contradiction. This refutes exact
attainment without the sign premise, not approximate or uniform existence.

## Source correspondence and Lean handoff

The credited source manuscripts are `AUXILIARY_CAP_DESCENT_AND_EXACT_LIMITS.md`,
`WEAK_SINGLETON_PAYOFF_EXCLUSION_AND_DETERMINANT_SELECTOR.md`, and
`TWO_PAIR_PAYOFF_EXCLUSION_AND_GEOMETRIC_FINITE_MENU_SELECTION.md`.
Their mathematical inputs used here are proved in full above. The separate
`CAP_THRESHOLD_DEBT_DESCENT.md` supplies a different arbitrary-source finite
descent theorem and stronger minimum-cap margins; its proof is not assumed
by this packet.

The bounded source audit inspected the following declarations in place:

- `quittingUniformEquilibriumPayoffConjecture`
  (`UniformEquilibrium/Quitting/Conjecture/Basic.lean`), an open proposition.
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticDebt`
  (`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).
- `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`
  (`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`), the exact
  coordinate ledger already present in Lean source.
- `minimumTerminalSemantic_singletonMargin` and
  `minimumTerminalSemantic_auxiliaryNash_eq_allContinue`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`).
- `minimumTerminalSemantic_nonnegativeWeight_lowerBound` and
  `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`):
  the latter uses a fixed linear reward-table bound with two positive weights.
- `exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`):
  this already implies qualitative Fin4 weak exclusion. Our claims are
  constructive and quantitative strengthening, and a particular raw entrance.
- `twoDisjointFirstStoppingPairMasses_sqrt_sum_le_one` and
  `sqrt_exactFiniteFirstStoppingPairMass_add_sqrt_le_one`
  (`MathUE/Probability/IndependentFirstStoppingPair.lean`): the square-root
  entrance is existing mathematics; retaining the two crossed masses in
  (18) is a separate finite reward attachment.
- `quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
  `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
  (`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`),
  the exact actual-law and unrestricted-cap adapters.
- `quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq`
  (`UniformEquilibrium/Quitting/Terminal/StoppingLawExploitability.lean`).
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`),
  the fixed-target semantic consumer.
- `HasLowActiveQuittingRootQuitPayoff`
  (`UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`),
  a unit-level predicate Q_i≤1. The raw fixture is not a unit-singleton
  table, so its own-singleton comparison above is not a failure of this
  predicate on the untransformed table. For the normalized terminal table
  r'_i(S)=(r_i(S)+t)/(s_i+t), t>0, all own singletons equal one, and the
  same pure B₀ root has active endpoints (1+t)/t>1. Thus that normalized
  table does fail the unit-level predicate. Never remains zero; no exact
  strategic equivalence under this terminal-only translation is asserted.
- `exists_uniformEquilibriumPayoff_of_lowActiveQuitPayoff`
  (`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`)
  requires both the unit-level predicate and `QuittingUnitSoloExit`. The
  raw fixture's satisfaction of the former alone therefore does not put
  it under that theorem: its singleton vector is (1,0,0,0).

The literature lane's README and model sections of
`Literature/SolanAndVieille2001.lean` and
`Literature/SolanAndSolan2020.lean` were inspected for scope. The former uses
zero Never; the latter permits a separate Never reward. This packet uses
zero Never throughout, invokes no unproved paper theorem as a project
theorem, and makes no literature-wide priority claim. Finite-game Nash
existence is its standard finite-dimensional existence input.

Both supplied Python scripts were completely read before execution. Their
`__main__` blocks write JSON outputs, so this review instead ran their pure
`verify()` and `run_checks()` functions through `runpy.run_path` with
`PYTHONDONTWRITEBYTECODE=1`. Both passed: 320 scalar identities, 1296 clock
products, all charged/solo cap regressions, and the auxiliary fixture's three
prefixes with total complete debt 1.388106540718527×10⁻⁷. These finite checks
are not proofs of the universal statements. No script output was overwritten.

A Lean implementation can begin with approximate-root version (2), forcing
(3), and rational or real finite-word selection. Its output should be
existence of actual words with total terminal debt below ε. The pair and
determinant predicates should take only reward-table data. The exact-limit
theorem should separately take the strict deficit and all-singleton signs,
construct one row sequence, and prove each suffix's full-response bound
using (7). Do not assume a selected sequence, cap continuity, or an exact
equilibrium as a structure field. Existing law adapters and the terminal
all-errors consumer then provide the semantic conclusion.

## Scope and nonclaims

These are ordinary mathematical proofs, not new Lean-checked declarations.
The source audit and finite arithmetic runs did not include a Lean build or
theorem-level axiom check. No theorem for arbitrary Fin4, no general exact
finite-menu Nash guarantee, no strategy-class completeness assertion, and
no cap-threshold quantitative collar is included. The strict-deficit exact
equilibrium conclusion requires every singleton reward to be nonnegative;
weak exclusion alone supplies the stated approximate finite selectors.
