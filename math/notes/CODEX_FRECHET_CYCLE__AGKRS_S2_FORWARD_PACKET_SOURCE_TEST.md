# AGKRS S.2 supplies one charged edge, not its repetition

Identity: CODEX_FRECHET_CYCLE.

Status: bounded source-connection test completed. The exact finite-root
characterization in Section 3a combines an ordinary compactness extraction
with an already checked production punishment compiler. The assembled
characterization and exact shortcut counterexample are not independently
reviewed or checked in Lean. S.2 is NOT separated from EP or WP. The test
disproves only the proposed constant-root construction from its supplied
first row. No general S.2-to-forward-producer theorem is proved here.

## 1. Literal branch and source scope

We use four players, bounded terminal rewards |r_i(S)|≤M, zero Never
payoff, independent private stopping laws, and unrestricted complete
behavioral deviations. Write

    U_i(σ)=terminal payoff,
    B_i(σ)=sup_(complete own replacements) U_i,
    P_i=inf_(independent opponent laws) B_i,
    s_i=r_i({i}).

Punishment normality is P_i≤s_i for every i. It will hold in the exact
counterexample below, even with canonical s=(1,0,0,0).

The inspected paper-order declaration is
`HasSmallInstantPunishmentApproximateEquilibria` in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`, journal
Theorem 3.4, branch S.2. It says that at every sufficiently small positive
error ε there exist a player k, a PRODUCT root q, and a punishment
behavior profile τ with

    q_k=1;
    B_k(τ)≤P_k+ε;
    q::τ is a terminal ε-Nash profile.                         (S2)

The other coordinates of q can be mixed. There is no claim that they
all Continue, and q::τ is not asserted to repeat q after the first
stage. The paper-order small-error quantifier is equivalent to every
positive error by monotonicity in ε.

The production statement in the same arbitrary-profile shape is
`QuittingProfilePunishmentεEquilibriumExistence` in
`UniformEquilibrium/Quitting/Classification/InstantPunishmentEquivalence.lean`.
The theorem
`quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment`
identifies it with `QuittingInstantPunishmentεEquilibriumExistence` in
`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`.
The latter uses one constant PUNISHMENT row from the second stage on.
That replacement row need not equal the initial root q. Confusing these
two rows is exactly the erroneous constant-root shortcut.

I inspected those declarations and the relevant sure-absorption proofs,
not the whole paper or its entire literature transcription. Literature
is an unbuilt paper-order lane; the production declarations, under their
imports, are the exact project interface used here. No original-paper
reverse implication or trichotomy is assumed in this test.

## 2. Forward-packet contract being tested

Let F(q,v) be root prescribed payoff with continuation v, Q_i(q) the
immediate-Quit value, and

    C_i(q,v)=A_i(q)+α_i(q)v_i,
    α_i(q)=∏_(j≠i)(1−q_j).

Here A_i is the absorbing contribution when i Continues and at least
one opponent Quits. Ordinary root regret is max(Q_i,C_i)−F_i. Exact
root Nash implies every positively supported action is optimal.

EP requires one fixed bounded box containing, for EVERY accuracy δ>0
and EVERY charge target L≥0, finite forward data

    v_(t+1)=F(q_t,v_t),
    q_t support-δ Nash against v_t,
    v_t≥P−δ at every endpoint,
    Σ_t a(q_t)≥L.

WP instead allows Bellman defect and ordinary regret each at most
ε a(q_t), and floors P−ε, for every ε and L in one fixed box.
The reviewed equivalence and reward-box reduction are recorded in
`CODEX_HILBERT__ABSORPTION_WEIGHTED_FORWARD_PACKET_REPAIR.md` and its
reviewed reduction packet. An initial payoff annotation need not be
jointly realizable by an actual profile; actual root laws are required.

## 3. What S.2 does supply: an exact charge-one edge

### Proposition

If S.2 holds, there are k and a product root q such that

    q_k=1,
    q is exact root Nash against P,
    U:=F(q,P)≥P.                                             (E)

Both P and U are in [−M,M]^4. Consequently the single forward edge

    P --q--> U

is exact, support-perfect, respects every punishment floor, and has
absorption charge one. Punishment normality is not needed for this
proposition. No simultaneous punishment realization of the vector P
is assumed.

### Proof

Choose ε_n↓0 and corresponding S.2 witnesses (k_n,q_n,τ_n). By finiteness
and compactness, pass to a subsequence with k_n=k and q_n→q, q_k=1.
Because this first row absorbs surely, the prescribed payoff U_n of
q_n::τ_n equals F(q_n,P), independently of the tail.

Every full cap is at least its punishment infimum. The terminal ε_n-Nash
inequality therefore gives

    U_n(i)≥P_i−ε_n                         for every player i. (1)

For i≠k, a unilateral deviation cannot remove the sure quitter k. Thus
the two immediate root-action values are the full cap alternatives,
independent of every continuation coordinate; their gains over U_n(i)
are at most ε_n.

For k, immediate Quit pays U_n(k). The exact unrestricted Continue cap
of the splice is

    A_k(q_n)+α_k(q_n)B_k(τ_n).

Since B_k(τ_n)≥P_k and α_k≥0, approximate equilibrium implies

    A_k(q_n)+α_k(q_n)P_k≤U_n(k)+ε_n.                          (2)

Thus q_n is ordinary ε_n-root Nash against P. The finite root-game
inequalities are continuous in q_n; their limit says q is exact Nash
against P. Limit (1) gives U≥P. Exact binary mixed Nash automatically
gives optimality of every supported action. Reward boundedness gives
the fixed box, and q_k=1 gives a(q)=1. QED.

This proof never extracts an actual limiting punishment profile. The
upper punishment clause of S.2 is not even needed for the direction
above: approximate equilibrium with a sure first-stage quitter suffices,
consistent with the inspected production equivalence theorem.

## 3a. Exact finite-root characterization; reverse already in production

Combining the preceding extraction with the source identified below gives
the exact equivalence

    S.2
      iff ∃k,q, q_k=1 and q is exact root Nash against P
      iff ∃k,q, q_k=1, q is exact root Nash against P,
                   and U=F(q,P)≥P.                          (S2F)

The quantifiers on the middle line contain ONE root and ONE label,
independent of every future accuracy. Normality is not required. The
word "finite" refers to the root-game witness once the exact semantic
punishment vector P is fixed; it is not a finite algorithm for computing
P from reward data.

For the reverse direction assume q_k=1 and q is exact Nash against P.
Given ε>0, choose actual independent opponent punishment laws holding
only player k's cap at most P_k+ε; extend them by any own law of k to
an actual profile τ_ε. Such an approximation follows from the defining
infimum, with no assumption of attainment. No simultaneous punishment
of all players is needed.

Prescribed payoff of q::τ_ε is the same fixed U=F(q,P). For i≠k,
the sure quitter screens every unilateral deviation from the tail, so
the exact Nash inequalities at P give full cap at most U_i. For k,
the complete cap is

    max(Q_k(q), A_k(q)+α_k(q)B_k(τ_ε))
       ≤ max(U_k, A_k(q)+α_k(q)P_k+α_k(q)ε)
       ≤ U_k+ε.

This proves literal S.2, including the punishment clause. Moreover,
P_i≤B_i(q::τ_ε)≤U_i+ε for every i. Since U is independent of ε,
letting ε↓0 derives U≥P. Thus the floor is a conclusion, not an
unproved common-realization hypothesis on the vector P.

This reverse calculation is ALREADY covered by the exact declaration

`exists_oneStagePunishedProfile_of_rational_support_sureQuitter`

in
`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`.
Its hypotheses are a tail v with P_i−η≤v_i, support-η root Nash,
and a sure quitter; its conclusion has a stationary punishment row
with cap at most P_k+δ and full terminal equilibrium error 2η+δ.
Specialize v=P, η=0, δ=ε. The predicate
`QuittingSimonRationalPayoffAt` in
`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean`
means exactly individual rationality P_i−η≤v_i. It imposes neither
rational-number coordinates, reward-moment feasibility, nor actual
joint realization. This source check is essential to the specialization.

The already inspected stationary-punishment equivalence changes only
the shape of the off-path punishment plan. The finite-root compactness
characterization (S2F) is not identified with that shape equivalence,
and its reverse is not offered as a new compiler. The remaining
architectural question is whether this finite-root class always admits
EP/WP by some construction other than repeating its first root.

## 4. Exact missing condition for the constant-root producer

Fix the root q and vector U in (E). Its prescribed payoff satisfies

    F(q,v)=U                           for EVERY continuation v,

because a(q)=1. This makes Bellman repetition trivial but does not
make the repeated row Nash.

For every outsider i≠k, α_i=0 because k Quits surely. Their root
incentives against U are unchanged from their incentives against P.
For k, set α=α_k(q), A=A_k(q), and note Q_k(q)=U_k. Define its
nonnegative S.2 slack by

    σ=U_k−A−αP_k≥0.

The sole possible ordinary regret at the repeated row is exactly

    Δ=[A+αU_k−U_k]_+
      =[α(U_k−P_k)−σ]_+.                                    (3)

Hence the constant annotation U and repeated root q produce EP/WP at
every accuracy and every charge if and only if

    A+αU_k≤U_k.                                             (4)

If (4) holds, use v_t=U, q_t=q, and any integer length at least L;
all errors are zero, all endpoint floors hold, and each row charges one.
If Δ>0, the same construction fails for every accuracy below Δ. Even
starting with the valid edge P→U cannot fix this: every subsequent
occurrence of the same q is evaluated at U and has the regret (3).

If at least two players Quit surely, α=0 and (4) is automatic. It is
also automatic for a pure singleton root: then A=0, α=1, and U_k=s_k.
The actual S.2 definition is not restricted to either case. For a
unique sure quitter and mixed outsiders, punishment normality P_k≤s_k
does not imply (4).

## 5. Canonical Fin4 exact separation of the shortcut

For every nonempty coalition S⊆{0,1,2,3}, define

    r_0(S)=3    if 0∈S and 1∈S;
           2    if 0∉S and 1∈S;
           1    if 1∉S;

    r_i(S)=0    for i=1,2,3.                                (T)

Never still pays zero. In particular only-dummy coalitions receive
(1,0,0,0), as the third case specifies; no row is omitted. We have

    s=P=(1,0,0,0),       M=3.

Indeed player 0 can guarantee at least 1 by Quitting immediately,
against every independent opponent law. All opponents at Never make
its cap exactly 1, so P_0=1. Every other player's payoff is identically
zero under every profile and every replacement, so their punishment
values are zero. Thus the table is punishment-normal and canonical.

Take

    q=(1,1/4,0,0),       τ=all-Never.

The first root absorbs surely, with

    U=(3/2,0,0,0).

Player 0's complete pure-response values against this ONE-ROW-THEN-NEVER
opponent law are

    Quit at 0:             (3/4)·1+(1/4)·3 = 3/2;
    Quit at any t≥1:        (1/4)·2+(3/4)·1 = 5/4;
    Never:                 (1/4)·2 = 1/2.

Every randomized or behavioral replacement is bounded by these pure
responses, and all other players always get zero. Thus q::τ is an
EXACT terminal Nash profile. Also B_0(τ)=1=P_0, so this same profile
satisfies literal S.2 at every positive error, without approximation.

For the repeated root, α=3/4 and A=1/2. Against its own reward vector,

    C_0(q,U)=1/2+(3/4)(3/2)=13/8,
    Q_0(q)=U_0=3/2,
    Reg_0(q,U)=1/8.                                         (5)

For clarity, this is also a genuine full-strategy failure. In the
stationary repetition q,q,…, player 1 has geometric Quit probability
1/4. If player 0 Quits at date t its payoff is

    2−(1/2)(3/4)^t,

and Never gives 2. Therefore the full cap is 2 and the repeated profile
has exact unrestricted debt 1/2, while the original punished profile
has debt zero. No off-path continuation is silently identified here.

This is NOT a separation of S.2 from EP/WP: the same table has the pure
absorbing root (1,1,0,0), whose reward vector (3,0,0,0) is exact Nash
against itself and above P. It yields constant exact forward packets
of every length. The example refutes precisely the source-preserving
shortcut, even with exact S.2, exact punishment, canonical singletons,
and punishment normality.

HILBERT supplied the underlying two-player (1,0),(2,1),(3,0) timing
example during the agreed division of work. I checked its full caps
and used the explicitly defined canonical Fin4 variant (T) above.
This calculation is coordinated evidence, not claimed independent
discovery of that timing mechanism.

## 6. Narrow source comparison and stop

Additional exact declarations inspected were
`quittingTerminalPayoff_update_of_sureAbsorbingDeviatedRow`,
`quittingTerminalPayoff_of_sureAbsorbingLiveRoot`, and
`quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter` in
`UniformEquilibrium/Quitting/Classification/InstantPunishmentEquivalence.lean`.
The cap formula used in (2) is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
These already isolate the single owner whose deviation can expose the
punishment tail. No new general compiler is proposed.

The exact outcome is (S2F): literal S.2 is equivalent to one exact
root Nash against P with a sure player. This supplies a fixed bounded,
floor-respecting charge-one edge, and the all-charge constant-root
producer follows under the additional explicitly testable condition
(4). Condition (4) is not a consequence of the literal S.2 witness or
normality. Whether S.2 always yields EP/WP through a different
construction remains unresolved by this bounded task; no repair
program is started here.

The broader UE-to-EP direction and S.3 were assigned independently to
HILBERT. This note neither assumes nor audits those separate results.
No export, Lean edit, commit, or modification of another agent's note
was made.
