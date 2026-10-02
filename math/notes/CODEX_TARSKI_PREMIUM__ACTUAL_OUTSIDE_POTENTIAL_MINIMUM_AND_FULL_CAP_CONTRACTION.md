# An actual outside-potential minimum with all-root full-cap contraction

Author: CODEX_TARSKI_PREMIUM.

Status: complete ordinary proof, independently reviewed but not
Lean-checked. Restricting outside minimization to the compact ACTUAL
prescribed-payoff image is legitimate without convexifying that image.
Literal solo prefixes supply the missing entrance below its singleton
boundary. Every exact root at the selected actual payoff crosses to the
strict singleton interior and uniformly contracts every full behavioral
regret of EVERY profile realizing that payoff. This is an actual strict
improvement whenever the input maximum regret is positive, not a renewable
selector, a cap-preserving compression, or
a near-global-minimum source. No export or UE class is claimed.

## 1. Exact data and the genuine additional question

There are four players. Each nonempty stopping coalition S has reward
r(S)∈[−M,M]^4, where M>0; Never and preabsorption rewards are zero.
Players use independent private behavioral strategies and face arbitrary
complete behavioral deviations. Write U(σ) for the terminal payoff and

    Y={U(σ): σ an actual independent behavioral profile},
    s_i=r_i({i}),       K=[−B,B]^4,       B>M,
    C={v∈K: v_i≥s_i for every i},
    C⁺={v∈K: v_i>s_i for every i},
    L=C\C⁺.

The production payoff-closure theorem says that Y is compact and every
point of Y has an exact independent finite-calendar representative. For
four players one may use dates 0,…,19 and Never. This preserves the four
PRESCRIBED payoffs only. We infer no cap or debt equality between different
representatives.

For a root q∈[0,1]^4, let c(q)=∏_i(1−q_i), a(q)=1−c(q), and

    F(q,v)=c(q)v+Σ_(S≠∅) Pr_q(S) r(S).

Q_i(q) and C_i(q,v) are the actual finite root Quit and Continue endpoints.
Exact root Nash means F_i(q,v)=max(Q_i(q),C_i(q,v)) for all four players.
Assume H is C¹ on a neighborhood of K and satisfies

    H(v)−H(F(q,v))≥a(q)                                 (D)

for EVERY exact root Nash q at EVERY v∈K. The universal robust polynomial
certificate supplies (D), but the present proof needs only these exact
edges and C¹ regularity. Neither actual punishment normality nor the
no-sure alternative is additionally needed for the statements below.

The earlier ambient outside minimum need not be in Y. Conversely, the
earlier unrestricted minimum of H on Y is root-inert. The question here
is whether restriction to the ACTUAL outside region supplies a root-active
actual source. An arbitrary coordinate lowering is not an allowed move
in Y and will not be used as one.

## 2. The two legal prefix facts

If v=U(σ)∈Y and q is ANY product root, independently prefixing q to σ
is a literal behavioral profile with payoff F(q,v). Hence

    F(q,v)∈Y.                                           (2)

No Nash property is needed for this payoff-closure operation. In
particular, for p^i=r({i}), a solo-i prefix of probability t gives

    v(t)=(1−t)v+t p^i∈Y,          0≤t≤1.                (3)

This is a genuine one-player prefix segment. It does not establish
convexity of Y or permit arbitrary segments to multi-player coalitions.

We also use the ambient singleton-face consequence of (D):

    v∈C, v_i=s_i  ⇒  ∇H(v)·(v−p^i)≥1.                (4)

For completeness, if all other coordinates strictly exceed their s,
a sufficiently small solo-i root is exact Nash at v. The active owner
is indifferent; every other player strictly prefers Continue because
its positive initial slack dominates the O(t) joining change. Its
successor is (3), and (D), divided by t and sent to zero, proves (4).
For other pinned coordinates, replace each nonowner v_k by
(1−ε)v_k+εB. These annotations stay in K and have strict slack because
B>s_k. Apply the just-proved inequality and let ε decrease to zero.
C¹ continuity gives (4). These auxiliary annotations need NOT lie in Y:
they are used only to derive the ambient consequence of the assumed
ALL-annotation inequality. The actual perturbation used below is (3).

## 3. Nonemptiness of the actual singleton boundary

First minimize H on compact nonempty Y, obtaining b. For any exact root
at b, (2) and minimality give H(F(q,b))≥H(b). Thus (D) forces a(q)=0.
Finite-game Nash existence makes this nonvacuous and shows that all
Continue is Nash at b, whence b∈C.

In fact b∈C⁺. If b_i=s_i, the legal solo segment (3) and global
minimality on Y imply

    ∇H(b)·(p^i−b)≥0.

This contradicts (4). Thus every coordinate of b is strictly above its
singleton.

Choose any i and follow the legal segment from b to p^i. At its initial
point all singleton inequalities are strict, while at its final point
the i coordinate equals s_i. The continuous function
min_k(v_k(t)−s_k) starts positive and is nonpositive at t=1. At its
first zero the whole vector lies in L. By (3) that vector is in Y.
Therefore Y∩L is nonempty; it is compact because Y and L are compact.
This argument does not assume that an arbitrary singleton reward vector
itself lies in C.

## 4. An actual strict-outside minimum

Let x minimize H on Y∩L and write h_L=H(x). Pick a pinned coordinate
i with x_i=s_i. Along the actual solo segment (3), (4) gives

    d/dt H((1−t)x+t p^i)|_(t=0)≤−1.

Consequently, for all sufficiently small positive t,

    H((1−t)x+t p^i)<h_L.                                (5)

That entire segment keeps its i coordinate equal to s_i, so it lies in
Y\C⁺. The points satisfying (5) cannot belong to C, since then they
would be in Y∩L and violate the definition of h_L. Thus (5) gives a
literal actual payoff STRICTLY outside C, not a freely lowered vector.

Now Y\C⁺ is nonempty and compact. Minimize the SAME H there, obtaining
z and h_out=H(z). The preceding construction proves

    z∈Y\C,             h_out<h_L.                      (6)

For EVERY exact root q at z, a(q)>0: all Continue is not Nash because
some z_i<s_i. By (2), its exact successor w=F(q,z) is in Y, and (D) gives

    H(w)≤h_out−a(q)<h_out.

Minimality on Y\C⁺ therefore forces

    w∈Y∩C⁺  for EVERY exact root at z.                  (7)

This is the additional actual-source statement. No finite-law response
or cap has been transported through payoff compression.

## 5. What uniform bounds survive, and what does not transfer

The exact root set N(z) is nonempty and compact: the finite root
inequalities are continuous, and the root cube is compact. On N(z),
a(q)>0 and every F_i(q,z)−s_i>0. Hence there are constants a_*>0 and
ε_*>0, depending on this selected source, such that

    a(q)≥a_*,       F_i(q,z)−s_i≥ε_*  for all q∈N(z),i. (8)

Every q∈N(z) has at least two active players. A solo active player
receives its own Quit endpoint s_i, contradicting (7). Also, no exact
root at any annotation can have two sure quitters: every unilateral
endpoint would then be annotation-independent. At its own reward
successor that same root would be a charged self-loop, contradicting
(D). We will only need the at-least-two-active conclusion.

Define the player-deleted Continue factors

    c_−i(q)=∏_(j≠i)(1−q_j),
    κ=max_(q∈N(z),i) c_−i(q).

Each factor is strictly below one, because some OTHER player is active.
Compactness gives

    0≤κ<1.                                              (9)

These are honest source-dependent compactness bounds on a single finite
root set. The previous ambient δa floor slack does NOT automatically
transfer: lowering one successor coordinate to s_i may leave Y. Nor does
the ambient semiconvex chord argument transfer, since its boundary point
on the straight segment z→F(q,z) need not be in Y. We use neither bound.
There is no implied uniform rate over all tables or all H.

## 6. Complete behavioral-cap consequence on literal profiles

Choose ANY actual profile σ with U(σ)=z; in particular an exact
finite-calendar representative supplied by production is available.
Let B_i(σ) be the supremum over ALL complete behavioral deviations of
player i's terminal payoff against σ_−i, and put

    d_i(σ)=B_i(σ)−z_i≥0,       E(σ)=max_i d_i(σ).

For ANY q∈N(z), let σ'=q⊕σ be the literal independent root prefix.
The exact full-cap splice is

    B_i(σ')=max(Q_i(q), C_i(q,z)+c_−i(q)d_i(σ)).          (10)

An arbitrary response chooses Quit or Continue initially. In the latter
case its later complete response sees the unchanged actual tail only on
the player-deleted all-Continue event, whose probability is c_−i. Taking
the supremum gives (10), also when the supremum is not attained or that
event has zero probability. In particular Never and all late responses
are included; this is not just the two-action root regret of σ'.

Write G_i=Q_i−C_i(q,z). Since q is exact Nash,

    U_i(σ')=max(Q_i,C_i),
    d_i(σ')=[c_−i(q)d_i(σ)−max(0,G_i)]_+
             ≤c_−i(q)d_i(σ)≤κ d_i(σ).                 (11)

Thus the selected actual source has the ALL-representative/ALL-root
comparison

    E(q⊕σ)≤κ E(σ),           κ<1.                      (12)

For finite-calendar σ the prefix is another literal finite-calendar
profile, with its last possible played date shifted by one. No cap
comparison between distinct realizers of z is asserted.

## 7. Exact stopping point and source comparison

The output payoff w is strictly inside C and has H(w)<h_out. It is NOT
another minimizer over Y\C⁺. Hence (12) does not iterate by reusing this
source construction. Repeating the same root against w need not be
Nash, and replacing the tail by a different realizer of z may restore
the old caps.

This can be quantified without assuming any minimum is attained. Let
m=inf_τ E(τ) over all actual profiles. From (12),

    m≤κ E(σ) for EVERY actual σ with U(σ)=z.             (13)

If m>0, then κ>0 and this entire payoff fiber has E(σ)≥m/κ>m.
So the construction explicitly does NOT provide a near-global-minimum
cap source in the hypothetical positive-gap case. A contradiction would
need a justified return/reselection that preserves the gained cap bound,
or another comparison not requiring that return. Neither is supplied.

The prior
[actual-payoff localization](../notes/CODEX_FRECHET_CYCLE__ACTUAL_PAYOFF_CARRIER_POTENTIAL_LOCALIZATION.md)
already proves compact payoff realization and scalarized full-response
conditions at a GLOBAL minimum on Y. That source has only the zero exact
root. The new input is (5): the boundary minimum is lowered by a literal
solo prefix. It yields the different, actually realized outside source
(6), for which ALL exact roots have the strict all-owner contraction
(12). The general cap-splice identity itself is existing machinery.

Exact declarations inspected:

- `quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff`,
  `isCompact_quittingActualTerminalPayoffSet`, and
  `exists_sparse_finiteCalendarLaws_of_mem_closure_actualPayoff`, in
  `Quitting/Paths/FiniteCalendarPayoffClosure.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation` and
  `quittingTerminalSemanticDebt_prefix_eq_blockAct`, in
  `Quitting/Root/TerminalSemanticPair.lean`; these give the actual full
  semantic splice and the positive-part formula (11);
- exact root existence in `Quitting/Root/NashExistence.lean`;
- the universal-certificate route in
  `Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.

The internal
[singleton-face proof](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md)
supplies (4), rederived in §2. Its raw-class corollary is already covered
by the existing projective-Q-bar consumer and is not claimed anew here.
The earlier ambient crossing note is unchanged; no rate from it is
silently used on the nonconvex actual image.

Independent bounded review:
[NOETHER's full proof check](../feedback/CODEX_TARSKI_PREMIUM__ACTUAL_OUTSIDE_POTENTIAL_MINIMUM_AND_FULL_CAP_CONTRACTION__BY_CODEX_NOETHER_SUPPORT.md)
accepts all equations and source quantifiers at the original SHA
`aba2b72e5baf42723dcde4c9ce6d0d035091edd4de6e35da71991121f80b22d2`.
Its only requested clarification was the positive-input-regret qualification
in the introductory strict-improvement sentence, now incorporated. Exact
arithmetic additionally checked (10) in 360 full-cap coordinates and (11)
for 81 literal finite-tail Nash prefixes, enumerating every distinct
finite deadline and Never; these are formula tests, not H fixtures.
