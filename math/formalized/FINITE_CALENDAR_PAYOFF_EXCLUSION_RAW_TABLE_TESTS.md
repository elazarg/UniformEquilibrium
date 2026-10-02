# Finite-calendar reward-table tests for payoff-exclusion selectors

## 1. Exact output and finite data

Fix four players I={0,1,2,3}. Every nonempty quitting coalition S pays
r(S)∈ℝ⁴; preabsorption and all-Never pay zero. Write s_i=r_i({i}) and fix
M>0 bounding the absolute values of the sixty reward entries. All players
and unilateral deviators may use arbitrary behavioral strategies with
independent private randomization. Equivalently, on the unique live history
they use independent laws on ℕ∪{∞}, where ∞ means Never. No public mixture
or correlated selection is available.

For an actual profile p, let U(p) be its prescribed terminal payoff. The
three hypotheses to be recognized are:

- PD: ∃κ>0, every finite word p has min_i(U_i(p)−s_i)≤−κ.
- GE: ∃β<1, every finite word p admits a probability vector w with
  max_i w_i≤β and Σ_i w_i(U_i(p)−s_i)≤0.
- WE_J: fixed nonempty J⊆I has s_i≥0 for i∈J, and every finite word p
  has U_i(p)≤s_i for some i∈J. Singletons outside J may have either sign.

A finite word consists of finitely many independent product rows followed
by all-Never. A fixed prescribed collection of admissible GE weights can
only strengthen its hypothesis: allowing the full capped simplex gives
exactly the existential class above, because that full simplex itself is
one permissible collection.

The result below replaces all finite-word quantifiers by the explicit
twenty-date polynomial predicates (P), (G), and (W). These are equivalent
tests of the same hypotheses, not new sufficient relaxations. Section 5
proves that accepted tables admit actual finite-law selection
against every complete behavioral deviation and a fixed uniform-equilibrium
payoff. The equilibrium words themselves need not have twenty
dates. Rational tables admit exact decision of these three predicates in
principle by finite real quantifier elimination.

## 2. Payoff realization on one fixed finite calendar

We prove the needed dependency for n≥1 players, with K=n(n+1). Put

    C_r={U(p): p is any actual independent stopping-law profile}.

Theorem 2.1. Every point of closure(C_r) is the payoff of one actual profile
whose finite stopping dates lie in {0,…,K−1}, with Never also allowed.
Each player's realizing marginal can additionally have at most n+1 support
actions, counting Never. Thus C_r itself is compact and is the image of one
fixed finite product simplex. For Fin4, K=20.

Proof. Censor each original marginal after a cutoff, moving only its finite
tail mass to Never. That changed mass tends to zero even when the original
Never mass is positive. Independent coupling bounds the change of each
bounded payoff by 2M times the sum of these finite tail masses. Therefore
finite-law actual payoffs approximate all actual payoffs; by choosing a
cutoff separately for each member of a convergent sequence they approximate
every point of closure(C_r).

For one finite-law product profile, hold all but player i fixed. Its WHOLE
payoff vector is a convex combination of the vectors obtained when player
i instead uses one of its currently supported pure dates or Never. There
are finitely many such vectors in ℝⁿ. A combination with more than n+1
positive weights has an affine dependence: move weights along that
dependence, preserving their sum and vector, until one first becomes zero.
Iteration gives at most n+1 currently supported actions. This operation
preserves all n prescribed payoffs, not only the mixer's own payoff.

Do this successively for all n players against their CURRENT opponents.
Later operations do not enlarge any earlier support. Every operation
preserves the same whole vector, and there is one independent product
profile throughout. The union of its finite support dates has size at most
n(n+1). Apply one increasing rank map from that union to {0,…,K−1}, fixing
Never, to every marginal. It preserves all comparisons and ties among
realized clocks, so it preserves the first quitting coalition pointwise.
This transforms each marginal separately and preserves independence.

The resulting profiles all lie in one fixed finite product simplex. Its
subset with marginal support size at most n+1 is a finite union of closed
products of simplex faces, hence compact. The prescribed-payoff map is a
polynomial on this space. A subsequential limit of the compressed finite
approximants therefore realizes the desired closure point exactly, retaining
the support bound. Conversely every such finite profile is actual. QED.

Only prescribed payoffs are retained by this construction. No cap
coordinate enters the finite observables.

## 3. Explicit polynomial data and exact predicates

Return to Fin4. Use eighty-four real variables x_i,t, with i∈I and
t∈{0,…,19,∞}. Define the product-simplex condition

    Δ(x):  x_i,t≥0 for every i,t, and Σ_t x_i,t=1 for every i.

For each nonempty S⊆I put

    P_S(x)=Σ_(t=0)^19 [∏_(i∈S)x_i,t]
                         [∏_(j∉S)(x_j,∞+Σ_(u=t+1)^19 x_j,u)],
    P_∅(x)=∏_i x_i,∞,
    V_i(r,x)=Σ_(S≠∅) P_S(x)r_i(S),
    A_i(r,x)=V_i(r,x)−s_i.

The P_S are degree-four polynomials in x. Their events are the disjoint
first-quitting-coalition events, so Σ_S P_S=1. The functions V_i are
polynomial jointly in the raw table and x, and linear in the table for fixed
x. Theorem 2.1 says C_r={V(r,x): Δ(x)} EXACTLY.

Every x is an executable twenty-row product word: at live date t use hazard
x_i,t/(x_i,∞+Σ_(u≥t)x_i,u) when the denominator is positive, and zero
otherwise. Subsequent rows are all-Continue. Conversely any finite product
word yields independent finite clock laws by multiplying the preceding
survival probabilities. Thus the finite-calendar image is contained in the
finite-word image, and Theorem 2.1 gives equality with the payoff image of
ALL finite words and even all unrestricted actual profiles.

### Strict deficit

Define the raw-table predicate

    (P)  there is NO x satisfying Δ(x) and A_i(r,x)≥0 for every i.

Then (P) is equivalent to PD. For the nontrivial direction, the continuous
function f(x)=min_i A_i(r,x) is strictly negative at every x∈Δ by (P).
Compactness gives max_Δ f<0; take κ=−max_Δ f>0. The resulting bound applies
to every actual profile by exact payoff realization. The converse follows
because a nonnegative surplus vector contradicts every positive κ.

For a SUPPLIED κ>0, the exact predicate is instead

    ∀x, Δ(x) ⇒ [∨_i A_i(r,x)≤−κ].                       (Pκ)

Using A_i>0 in the forbidden system (P) would characterize only weak
exclusion, and is not a valid strict-deficit test.

### Weak subset exclusion

For supplied nonempty J define

    (W_J)  [s_i≥0 for all i∈J], and there is NO x with
           Δ(x) and A_i(r,x)>0 for every i∈J.

This is equivalent to WE_J by exact payoff realization, without a margin or
closure approximation. If the problem is to recognize the existence of a
witnessing subset, it suffices to take the maximal allowed set

    J₊={i:s_i≥0}.

The existential subset version holds iff J₊ is nonempty and (W_J₊) holds:
enlarging a witnessing subset preserves its disjunction. Equivalently one
may use the finite disjunction of (W_J) over the fifteen nonempty subsets.

### Nonconcentrated group exclusion

For λ∈(0,1/2] define twelve ordered-pair polynomials

    L_ij(r,x,λ)=(1−λ)A_i(r,x)+λ A_j(r,x),   i≠j.

The exact raw-table predicate is

    (G)  ∃λ, 0<λ≤1/2 and
         ∀x, Δ(x) ⇒ [∨_(i≠j) L_ij(r,x,λ)≤0].         (G)

Equivalently, some such λ makes the finite polynomial system
Δ(x), L_ij(r,x,λ)>0 for EVERY ordered pair i≠j infeasible.

Proof of equivalence to GE. Any admissible β can be enlarged to
β'=max(β,1/2)<1. Put λ=1−β'. For any surplus vector a, let i index its
smallest coordinate and j a smallest coordinate outside i. For every
probability weight with each coordinate at most β',

    Σ_k w_k a_k ≥ w_i a_i+(1−w_i)a_j
                ≥ β'a_i+(1−β')a_j.

Equality is attained by the admissible weight β'e_i+(1−β')e_j. Hence the
minimum over the capped simplex equals min_(i≠j)[(1−λ)a_i+λa_j]. GE
therefore implies (G). Conversely a pair witnessing (G) gives exactly an
admissible probability weight with β=1−λ<1. This holds profile by profile,
with one uniform λ but without requiring one fixed pair. QED.

The quantifier order ∃λ∀x is essential. Replacing it by ∀x∃λ would not
supply the uniform nonconcentration parameter used in Section 5. Pairs must
be distinct; i=j would silently allow concentrated weights.

## 4. Semialgebraic recognition and finite certificate interface

For the sixty raw reward variables, (P), (W_J), and (G) are explicit
first-order formulas over the reals using the finite polynomial family
above. Real quantifier elimination therefore makes their truth sets
semialgebraic, and decides membership for rational or real-algebraic input
tables in principle. This is an application of the real closed field
decision theorem, not a claimed new algorithm or an efficiency result.
No expanded quantifier-free formula or implemented solver is claimed here.
For arbitrary unencoded real input the statements remain exact mathematical
equivalences, not computational promises.

The interface supplies all quantitative parameters needed by the consumers:

- If (P) is accepted for a rational table, some rational κ>0 satisfies
  (Pκ). After recognizing (P), testing κ=1/k for k=1,2,… terminates.
- If (G) is accepted, some rational λ∈(0,1/2] works. Indeed the minimum
  pair value is a_(1)+λ(a_(2)−a_(1)), which is nondecreasing in λ.
  Any smaller positive λ remains valid. After recognizing (G), testing
  λ=1/k for k=2,3,… terminates. Set β=1−λ.
- (W_J) requires no positive separation margin. Equality cases are accepted
  exactly; finite sampling alone is not a decision procedure for this test.
- A rational M larger than every absolute reward is immediate. Positive
  error tolerances can likewise be taken rational.

Every individual test in these searches is the finite real-algebraic
predicate just displayed. Rejection of (P) has an actual twenty-date
witness with every surplus nonnegative; rejection of (W_J)'s exclusion
clause has one with every surplus in J strictly positive. For rational
tables real-algebraic witnesses can be chosen in these semialgebraic sets.
Their laws are genuine independent laws. Rejecting (G), by contrast, need
not give ONE profile defeating every λ: its exact negation retains
∀λ∃x. No contrary single-witness assertion is made.

## 5. Actual finite selectors and their complete-response proofs

For every accepted (P), (G), or (W_J), and every ε>0, there is an actual
finite word p whose total complete-deviation debt is less than ε. The
construction below also gives geometric decay under PD, reciprocal decay
under GE, and a reward-bound-only weak-selection rate. Under PD and
nonnegative own singletons for all players, one infinite profile is exact
terminal Nash at every suffix and uniform at its initial terminal payoff.

Write n=4, B_i(p)=sup_τ U_i(p[i←τ_i]), d_i=B_i−U_i, and D=Σ_i d_i.
Every supremum ranges over complete behavioral replacements, including
unbounded stopping laws and Never. For the construction, WE denotes WE_J;
the set J and its singleton signs remain fixed. Choosing a working
accuracy below the requested one turns a weak debt bound into D<ε.
The bounded payoff realization in Section 2 is used only to prove the
exclusion hypotheses. Every newly constructed word's caps are computed
afresh from its actual rows.

### 5.1 Complete-prefix budget and rational roots

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

Equation (2) supplies both a literal iterative producer and an explicit
approximate-root error budget.

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

### 5.2 Strict-deficit selection and exact suffix limits

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

### 5.3 Nonconcentrated group selection

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

### 5.4 Weak-subset selection with a reward-uniform bound

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

### 5.5 Fixed uniform-equilibrium payoff

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

### 5.6 A fixed-table cap-threshold alternative

When every s_i≥0 and (W_I) holds, there is also a selector with a bound
depending on the table's strict preemption gaps. An owner i is preempted
when some j≠i has s_j−r_j({i})>0.

If every owner is preempted, put

    D₀=Σ_i s_i,    C₀=(128M+24D₀)/3,
    ell=min_i max_(j≠i)(s_j−r_j({i}))>0.

For rational table data and 0<ε<D₀, one actual rational word has D≤ε and
at most

    ceil(C₀/ε) [1+ceil((32(M+D₀)/ε) log(4M/ell))]

dates. This is the specialization to all four owners of
`executableRationalSelectedOwnerFirstWord_actualDebt_nash_and_length_le`
in `UniformEquilibrium/Quitting/Paths/ExecutableRationalWeakSubsetSelection.lean`.
Its hypotheses are exactly rational finite-word owner exclusion, strict
preemption of the designated owners, a positive rational reward bound,
and positive rational accuracy. Section 3 supplies the exclusion.
The definition `executableRationalSelectedOwnerUniformPhaseRowBound`
in `UniformEquilibrium/Quitting/Paths/ExecutableRationalSelectedOwnerRates.lean`
is the second factor displayed above. The preemption floor is produced
from the finite table by taking the minimum of the maximum blocker gaps;
it is not an extra strategic witness.

If some i is unpreempted, use K dates of solo-i hazard t and then Never.
Its own regret is at most M(1−t)^K because s_i≥0. For j≠i let
v_j=r_j({i})≥s_j≥0. Its cap is at most v_j+2Mt and prescribed payoff
is (1−(1−t)^K)v_j, so every player's regret is at most
2Mt+M(1−t)^K. Choosing

    t=min(1/2,ε/(4nM)),    M(1−t)^K≤ε/(2n)

gives D≤ε after finitely many rows, with rational tests on rational data.
This unblocked branch needs no exclusion hypothesis. Its real-table
existence counterpart is
`exists_finiteWord_debtSum_le_of_nonnegative_unpreemptedDesignatedOwner`
in `UniformEquilibrium/Quitting/Paths/FiniteUnpreemptedSoloExit.lean`.
The proof above supplies the geometric-tail bound directly. Section 5.5
gives the fixed uniform-payoff conclusion for either branch.

### 5.7 Sign-free qualitative four-player consequence

There is a broader QUALITATIVE Fin4 consequence already supplied by current
Lean mathematics. Even without sign assumptions, if some nonempty J has
no actual payoff strictly above s on J, the current strict-minimum plateau
theorem contradicts a hypothetical absence of uniform-equilibrium payoff.
Indeed that theorem supplies a semantic-carrier point whose prescribed
coordinates are strictly above every singleton. The carrier is the closure
of actual (U,B) pairs; projecting an approximating sequence puts that payoff
in closure(C_r)=C_r. Theorem 2.1 gives an actual bounded-calendar payoff
witness, contradicting the test. Only the payoff projection is realized;
the plateau's caps are not assigned to the realizing profile. This
qualitative implication was already available by approximating its strict
gap. It is not a new unrestricted selector with signed witnessing owners.

## 6. Boundary tests and exact scope comparisons

1. All-Never is x_i,∞=1; all prescribed payoffs are zero. A pure coalition
   at date zero is represented literally. The formulas keep these cases
   distinct, including the pure full-coalition tie.

2. PD is genuinely strict. Set s_i=1; at singleton {i} pay i one and
   everyone else minus one, and at every other nonempty coalition pay
   everyone minus one. Every actual payoff has coordinate sum at most zero,
   so min_i(U_i−1)≤−1 and PD holds with κ=1. In contrast, for the identically
   zero table PD fails at all-Never, while GE and every WE_J hold exactly
   on the equality boundary.

3. WE need not imply GE. Set r_0(S)=1 for every nonempty S. For j≠0 set
   r_j({0})=1 and r_j(S)=0 for every other nonempty S. Then s=(1,0,0,0)
   and U_0≤1 always, so WE_{0} holds. Pure {0} has surplus (0,1,1,1):
   every weight with max coordinate≤β<1 gives surplus ≥1−β>0.
   Thus GE and PD fail. This is a boundary example with an easy equilibrium,
   not an additional difficult game class.

4. GE properly goes beyond PD and the existing fixed nonnegative-weight
   reward-convex-hull criterion. Let A={0,1}, B={2,3}, with each player's
   partner in its pair. Set s_i=1 and

       r(A)=(2,2,1,1),       r(B)=(1,1,2,2).

   At singleton {i}, pay i one, its partner zero, and each outsider 1/2.
   At every remaining nonempty coalition pay every player 1/2. Let x,y be
   the actual terminal masses of A,B, ν the Never mass, and z=1−x−y−ν.
   The two group-average surpluses are x−z/2−ν and y−z/2−ν.

   Independence gives √x+√y≤1: compare clocks 0 versus 2 and independently
   1 versus 3. If their strict-order probabilities are a,b and a',b', then
   x≤aa', y≤bb', a+b≤1, a'+b'≤1; Cauchy–Schwarz proves the bound. If
   x≤y, put t=√x≤1/2. Then 3x+y≤3t²+(1−t)²≤1, so the first group
   surplus is (3x+y−1−ν)/2≤0. The other ordering uses the second group.
   This proves GE with β=1/2. Pure A has surplus (1,1,0,0), refuting PD.
   The half-A/half-B CORRELATED lottery has strictly positive surplus in
   every coordinate, refuting any nonzero nonnegative linear separator of
   the full reward convex hull. That lottery is not asserted to be actual.
   Pure A also fails the own-singleton product-low endpoint criterion:
   its two active players have Quit payoff 2>s_i. The unit-normalized
   source predicate is a different condition and is not identified with
   that own-singleton test here. This table itself has an easy pure A Nash
   equilibrium; failure of those tests is not a claim of an unsolved class.

5. PD implies GE for Fin4: if min_i a_i≤−κ and |a_i|≤2M, choose
   0<λ≤min(1/2,κ/(2M+κ)); weight 1−λ on a deficit coordinate and λ
   on any distinct coordinate. The weighted surplus is at most zero.
   If all singletons are nonnegative, GE in turn implies WE_I. Signed
   witnessing subsets must still satisfy their separate WE sign premise.

6. These tests do not decide UE existence. For example, pay every player
   one at its own singleton, two at the full coalition, and zero in all
   otherwise unspecified entries. Pure full quitting has surplus (1,1,1,1),
   so PD, GE and every WE_J fail; nevertheless that pure profile is exact
   terminal Nash because a sole player continuing instead receives zero.

7. Prescribed payoff preservation cannot be used to transport caps. In
   two players set r_0({1})=1 and every other reward entry zero. The pure
   profiles (0,1) and (0,∞) have the same terminal coalition {0} and payoff
   zero; player 0's response cap is respectively one and zero. Two inert
   Never players embed this test in Fin4. The adapter uses no such transfer.

## 7. Tracked semantic interfaces and handoff

The following tracked declarations give the relevant semantic interfaces:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingBehaviorStoppingLaw_finiteStoppingLawMixture` and
  `quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect` in
  `UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`:
  the latter explicitly covers every observer, supporting whole-vector
  affine replacement rather than only the mixer's own payoff;
- `quittingTerminalSemanticCarrier` and
  `exists_terminalProfile_sequence_tendsto_semanticPair` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`;
- `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`:
  its fixed weight has two positive coordinates and bounds every terminal
  row, including Never. Normalize that weight to see it is a special GE
  certificate; Section 6 gives exact strict separation of the conditions;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  actual terminal approximate Nash profiles at every positive error yield
  one fixed uniform-equilibrium payoff.

Finite affine support reduction and real quantifier elimination are the
classical ingredients in Sections 2–4. Their attachment to the proved
PD/GE/WE constructions turns an infinite collection of finite-word
hypotheses into a fixed-dimensional raw-table recognition problem, with
quantitative κ or β recoverable where needed.

No new qualitative class is claimed beyond the corresponding existing
payoff-exclusion implications; no global comparison against every normal-core,
non-Q, odd/even, or projective criterion is attempted. The evidence above
separates specific named conditions only. No recognized table is asserted
to lie outside all other known equilibrium results.

A Lean handoff can first formalize the fixed-calendar payoff realization,
then the polynomial first-outcome map and the three equivalences, and finally
compose them with the actual finite selectors proved in Section 5. Recognition
does not require a cap representation. No generic QE implementation is
needed to state or use the mathematical adapter; decision procedures can
remain an external classical consequence for encoded coefficients.
