# Normal equilibrium existence: forward packets or one sure root

Identity: CODEX_HILBERT. Ordinary mathematical composition, not checked in
Lean and not independently reviewed as a combined theorem. No export claim.

**Status.** Under punishment normality and a positive own singleton, the
disjunction EP or the exact sure-root certificate below is equivalent to
uniform-equilibrium-payoff existence. This is an architecture-completeness
statement, not an equilibrium producer. Whether EP alone is necessary remains
unsettled by these arguments.

## 1. Exact statement

There are four players I={0,1,2,3}, real rewards r_i(S) on every nonempty
coalition, |r_i(S)|≤M for one M>0, and zero reward on Never. Strategies
are independent stopping laws on ℕ∪{Never}; deviations replace one complete
law. Write U_i(p) for terminal payoff and define

    Cap_i(p)=sup_[own replacements μ_i] U_i(μ_i,p_−i),
    P_i=inf_[independent opponent laws p_−i] Cap_i(p),
    s_i=r_i({i}).

For a product root q∈[0,1]⁴ let p_q(S) be its product coalition law,
c(q)=p_q(∅), a(q)=1−c(q), and

    F(q,v)=Σ_[S≠∅] p_q(S)r(S)+c(q)v.

Writing p_(q,−i) for the opponents' product law, set

    α_i(q)=p_(q,−i)(∅),
    Q_i(q)=Σ_[T⊆I\{i}] p_(q,−i)(T)r_i(T∪{i}),
    L_i(q)=Σ_[∅≠T⊆I\{i}] p_(q,−i)(T)r_i(T),
    C_i(q,v)=L_i(q)+α_i(q)v_i.

The root is exact Nash against v when
max(Q_i(q),C_i(q,v))=F_i(q,v) for every i.

Define the **sure-root certificate C** by

    ∃k∈I ∃q∈[0,1]⁴,
      q_k=1 and q is exact Nash against P.                  (C)

The label and root are fixed before any accuracy. The vector P is the exact
semantic punishment vector, not a supplied feasible joint payoff. Thus (C)
is a finite-dimensional certificate relative to P, not a finite algorithm
computing P from the reward table.

Define **EP** to mean that one finite B≥M works for every δ>0 and Q≥0:
there are H≥0, v_0,…,v_H∈[−B,B]⁴, and product roots x_0,…,x_(H−1) with

    v_(t+1)=F(x_t,v_t)                                  (t<H),
    every supported root action is within δ of the
      better of Q_i(x_t), C_i(x_t,v_t)                   (t<H, all i),
    v_t(i)≥P_i−δ                                       (t≤H, all i),
    Σ_[t<H] a(x_t)≥Q.

The indexing runs outward through prefixes. No common chronology or actual
joint realization of annotations is required across packets.

Let UE denote existence of one fixed uniform-equilibrium payoff: for every
positive accuracy there is a behavioral profile and a finite threshold that
deliver that payoff and bound every unilateral deviation at every longer
finite horizon. The payoff is fixed before the accuracy.

**Theorem.** Assume P_i≤s_i for every i and s_j>0 for at least one j. Then

    UE  ⇔  [EP or C].                                   (1)

EP may equivalently be replaced by WP, the absorption-weighted version
defined in the frozen weighted-repair theorem. In (C), the extra clause
F(q,P)≥P can be added without changing the certificate.

## 2. The finite S.2 correspondence

The bounded independent correspondence check here used FRECHET's complete
[S.2 note](CODEX_FRECHET_CYCLE__AGKRS_S2_FORWARD_PACKET_SOURCE_TEST.md),
SHA-256 b947425076715ab4bf29832b9bd586b60ca2ab4bc0b6767b82d4425a45c100b0.
Its Section 3a is valid: literal S.2 is equivalent to (C). Neither normality
nor positive singletons is needed for this equivalence.

For necessity, take terminal ε_n-Nash profiles q_n::τ_n with ε_n↓0 and
a sure root player k_n. Compactness gives a fixed k and q_n→q with q_k=1.
Since the prescribed root absorbs surely, U_n=F(q_n,P), regardless of τ_n.
For i≠k, a deviation still encounters sure k at the root, so its cap is
exactly the larger root endpoint. For k, the Continue cap is
L_k(q_n)+α_k(q_n)Cap_k(τ_n), which is at least C_k(q_n,P). Thus q_n
is ordinary ε_n-root Nash against P. Pass the continuous inequalities to
the limit. Also P_i≤Cap_i(q_n::τ_n)≤U_n(i)+ε_n, giving F(q,P)≥P.
No limiting punishment law or jointly realized vector P is extracted.

For sufficiency, fix (k,q) in (C). For each ε>0 choose an actual independent
opponent punishment for k with cap at most P_k+ε, and extend it to a
profile τ_ε. The prescribed payoff of q::τ_ε is the fixed U=F(q,P).
Every i≠k has full cap at most U_i because its deviation cannot expose the
tail. Player k has full cap

    max(Q_k(q), L_k(q)+α_k(q)Cap_k(τ_ε)) ≤ U_k+ε.

This proves S.2, and terminal approximate Nash at every error. It also
derives U≥P by letting ε↓0 in P_i≤Cap_i(q::τ_ε)≤U_i+ε. No punishment
attainment, simultaneous punishment of four players, or equilibrium behavior
inside the punishment tail is needed.

The reverse is already covered by
`exists_oneStagePunishedProfile_of_rational_support_sureQuitter` in
`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`:
specialize tail=P, support error η=0, and punishment error δ=ε. The source
predicate `QuittingSimonRationalPayoffAt` in `SuppliedCorrespondence.lean`
means only P_i−η≤tail_i; it imposes neither rational coordinates nor joint
payoff feasibility. Exact Nash gives support-0 Nash, so every hypothesis is
supplied. The generic profile/constant-punishment equivalence is already
`quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment` in
`Classification/InstantPunishmentEquivalence.lean`.

The narrow lookup did not identify the complete compactness-based finite-root
equivalence as a named declaration. The exact instant criterion used in
`Classification/Existence/NegativeExceptionalOwnerInstantObstruction.lean`
concerns a pure singleton root, not every product root in (C). None of this
offers the existing punishment compiler as new mathematics.

## 3. Proof of the combined equivalence

For the forward implication, assume UE. The checked terminal-Nash
all-errors equivalence supplies actual terminal approximate equilibria at
every error. The checked forward trichotomy then gives one fixed S.1, S.2,
or S.3 alternative. No equilibrium existence is assumed elsewhere in this
necessity argument.

The complete ordinary proofs of the following two adapters are in
[the partial-converse note](CODEX_HILBERT__NORMAL_EQUILIBRIUM_TO_FORWARD_PACKET_PARTIAL_CONVERSE.md),
SHA-256 b9c9096f87bdd676f2cc94190a16ef35e2dcdbec6b6534c0d4f7c8303f573bda:

- S.1 gives stationary terminal e-Nash profiles. For e<s_j, each has
  positive root absorption a. Its actual payoff U and the constant
  annotation U+2e·1 have Bellman defect 2ea and ordinary root regret at
  most 3ea. Repetition gives arbitrary charge in the one box
  [−M−2,M+2]⁴. Hence S.1⇒WP⇒EP. No uniform lower bound on a is needed.
- S.3 gives row-perfect roots against their literal restarted terminal
  payoffs. At error η<s_j the checked null-tail alternative gives
  termination after every restart. Under normality, the bounded-spine
  floor lemma gives every continuation coordinate at least P_i−τ once
  η≤min(τ/2,τ²/(8M)). Support error is at most 2η. Every-restart
  termination forces divergent total absorption charge; reverse a long
  finite chronological segment to obtain EP in [−M,M]⁴.

The S.2 arm gives (C) by Section 2. This proves UE⇒EP or C.

Conversely, EP⇒UE is the existing finite-forward-packet consumer. If (C)
holds, Section 2 supplies terminal approximate Nash profiles at every
positive error, and the checked terminal-Nash all-errors equivalence gives
UE. These two sufficiency directions do not require normality or a positive
singleton. The only new assembly is their composition with the two necessity
adapters and the finite S.2 characterization.

The exact production sources inspected for this composition are
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
`QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`
in `Quitting/Classification/Existence/ApproximateEquilibriumForwardTrichotomy.lean`,
and `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`
with `QuittingFiniteForwardPacket` in
`Quitting/Projective/FiniteForwardProjectiveLasso.lean`. These paths are
relative to `UniformEquilibrium/`; their exact statements and imports, not
the paper's unbuilt transcription, are the dependencies used here.

## 4. What this does and does not change

This answers a limited completeness question: in the stated class, the
union of the forward-packet architecture and the already solved finite
instant architecture covers UE existence. It does not prove either
alternative from arbitrary reward data.

The live forward-packet question assumes the global SUM infimum
D_*=inf_p Σ_i(Cap_i(p)−U_i(p)) is positive, as well as normality.
Condition (C) is already impossible under D_*>0 by its terminal consumer.
Some singleton must be positive there: if all s_i≤0, all Never is exact
terminal Nash. Consequently allowing the extra (C) arm does not weaken the
remaining contrary-case producer obligation. Using (1)'s necessity direction
to obtain a packet under no-UE would simply invoke an unavailable UE premise.

There is no outstanding gap identified in this bounded composition, but the
two new necessity adapters and the combined theorem have not received an
independent full review or a Lean implementation. Without a positive
singleton the all-Never S.1 and null-tail S.3 cases remain unmatched by these
proofs. This is a limitation of the argument, not a necessity claim about
that hypothesis and not a counterexample to EP.

The concrete remaining mathematical question is whether normal (C)-tables
always admit EP by some other construction. FRECHET's exact canonical
example refutes repeating the supplied sure root but has another exact
periodic source, so it does not separate EP from UE. No new producer or
normal-table separation is claimed here.
