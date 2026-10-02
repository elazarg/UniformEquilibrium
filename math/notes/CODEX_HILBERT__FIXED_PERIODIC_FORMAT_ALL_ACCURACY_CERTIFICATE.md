# Fixed periodic formats: decidable all-accuracy certificates

Mathematics from the external EXACT_CERT submission, preserved by
CODEX_HILBERT with its reviewed input-scope clarification. Ordinary
mathematics, not a Lean implementation or a strategy-class completeness
theorem. The complete source was reviewed at SHA-256
`f6f5483188129ee41d9877297eda50cf1f4af32f815c9be4e0ef08bafa69e070`;
the [independent review](../feedback/EXACT_CERT__BY_CODEX_HILBERT.md)
records the exact source overlap.

## 1. Data and theorem

There are four players. An exactly given rational table r assigns a vector
in [−1,1]⁴ to every nonempty coalition. Independent stopping laws on
ℕ∪{Never} determine the first finite stopping coalition; all Never pays
zero. A unilateral deviation may replace the entire stopping law. Write
U_i(p) for prescribed payoff, B_i(p) for the full response supremum,
E(p)=max_i(B_i−U_i), and η(r)=inf_p E(p) over all independent laws.

Fix integers h≥0 and L≥1. A format consists of h arbitrary root rows
followed by an endlessly repeated block of L rows. Its parameters belong
to [0,1]^{4(h+L)}. Let p_x be its actual product stopping law and
F_(r,h,L)(x)=E(p_x).

**Theorem.** The graph of F_(r,h,L), including every boundary branch, is
effectively semialgebraic over the rational input. Hence the sentence

    Ψ(r,h,L):  for every ρ>0 there exists x with F_(r,h,L)(x)<ρ

is decidable by real-closed-field quantifier elimination. If accepted, then
η(r)=0, and for every positive rational ε a terminating procedure produces
four rational finite stopping laws with full exploitability below ε.

An accepted format need not have an exact equilibrium: the infimum over its
parameters need not be attained. The theorem does not assert that some
fixed format is accepted whenever η(r)=0. For arbitrary real table entries
the graph is still semialgebraic over those parameters, but an effective
verifier requires an exact coefficient input model.

## 2. Exact full-response semantics

For a product root q define p_q(S)=∏_{j∈S}q_j∏_{j∉S}(1−q_j),
c(q)=p_q(∅), and A_i(q)=Σ_{S≠∅}p_q(S)r_i(S). For player i's
opponents let p_{q,−i}(T) be their product coalition probability, and put

    λ_i(q)=p_{q,−i}(∅),
    g_i(q)=Σ_{T≠∅}p_{q,−i}(T)r_i(T),
    k_i(q)=Σ_T p_{q,−i}(T)r_i(T∪{i}).

Thus g is the absorbing contribution from Continue and k is the Quit
endpoint. These are rational polynomials in q.

For the periodic rows q⁰,…,q^{L−1}, set

    a_s=∏_{t<s}c(qᵗ),       C=a_L,
    A_i=Σ_{s<L}a_s A_i(qˢ).

The actual prescribed tail payoff is V_i=A_i/(1−C) if C<1 and V_i=0
if C=1. In the latter case every periodic hazard is zero. Merely requiring
the fixed-point equation V=A+CV would incorrectly allow arbitrary values.

For each player separately define deleted survival and reward ledgers

    b_(i,s)=∏_{t<s}λ_i(qᵗ),       Λ_i=b_(i,L),
    H_i=Σ_{s<L}b_(i,s)g_i(qˢ),
    K_(i,s)=Σ_{t<s}b_(i,t)g_i(qᵗ)+b_(i,s)k_i(qˢ).

The payoff from pure Quit at nL+s is

    H_i Σ_{ℓ<n}Λ_i^ℓ + Λ_i^n K_(i,s).

For Λ_i<1 this interpolates between K_(i,s) and H_i/(1−Λ_i), the
literal Never payoff. Its supremum over n and s is therefore

    D_i=max{H_i/(1−Λ_i), K_(i,0),…,K_(i,L−1)}.

For Λ_i=1 all opponents literally choose Never. In that separate branch
D_i=max{0,r_i({i})}. This branch is independent of whether i's own law
is proper. At Λ_i=0 the same interpolation formula is valid: first-period
responses give K_(i,s), and later periods give H_i.

Any complete behavioral response induces a stopping law, and its payoff
is an average of the pure finite-date and Never payoffs. Thus D_i is the
unrestricted cap, not a periodic-strategy cap.

Starting with (u_i,b_i)=(V_i,D_i), prepend the h rows in reverse order:

    u_i ← A_i(q)+c(q)u_i,
    b_i ← max{k_i(q), g_i(q)+λ_i(q)b_i}.

The cap recursion retains the deviator-deleted survival λ_i, even if the
prescribed joint survival is zero. It remains exact for a nonattained
continuation supremum. At the root F=max_i(b_i−u_i).

All these operations have finite semialgebraic graphs. Division is encoded
only on the positive-denominator branch by its cleared equality; the
zero-denominator branches are imposed separately. A finite maximum is
encoded by inequalities against every candidate and equality to one.
This proves the graph claim and permits the exact quantified test Ψ.

## 3. Rational selection and finite-law compilation

Assume Ψ holds and fix rational ε>0. Enumerate rational parameter vectors
until exact evaluation finds F<ε/2. This search terminates. Indeed Ψ
supplies a real vector with F<ε/4. Freeze precisely its zero periodic
coordinates and approximate its positive coordinates by positive rationals.
On that stratum all assertions C=1 and Λ_i=1 retain their truth values;
every remaining denominator is locally positive. Prefix coordinates enter
only polynomial and max operations. The full F is consequently continuous
relative to this stratum, whose rational points are dense. A rational
F<ε/2 witness exists. The enumeration need not know its stratum beforehand.
No continuity across the all-Continue boundary is asserted.

For a selected rational vector, write

    a_j^pre=∏_{t<h}(1−x_jᵗ),
    s_j=∏_{t<L}(1−q_jᵗ).

After K≥1 periods, the marginal mass assigned to **finite** dates at or
beyond N=h+KL is

    τ_j(K)=a_j^pre s_j^K   if s_j<1,
    τ_j(K)=0              if s_j=1.

In the second case all surviving mass was already Never. All τ_j tend
to zero. Choose K by exact rational search until 4Σ_jτ_j≤ε/2. Keep
each marginal's atoms below N and send its remaining finite mass to Never.
The output has rational atoms

    p_j(t)=x_j(t)∏_{v<t}(1−x_j(v)),  0≤t<N,
    p_j(Never)=∏_{v<N}(1−x_j(v)),

and N≥1. It is a single actual independent finite product law.

Couple old and censored clocks by changing only the finite tail events.
The prescribed payoff changes by at most 2Σ_jτ_j. For any replacement
law of i, coupling only its opponents bounds the response-payoff change
by 2Σ_{j≠i}τ_j, uniformly over that replacement. Taking full suprema
preserves this bound. Hence

    |E(p_x)−E(p)| ≤ 4Σ_jτ_j ≤ ε/2,

so E(p)<ε. Ties, preemption, Never, and arbitrarily late responses are all
included. For a known general reward bound M, replace 4 by 4M. Increasing
K also satisfies any prescribed lower deadline bound.

## 4. Exact unresolved quantifier

The finite pair (h,L), checked by Ψ, certifies all accuracies, not one
accuracy. The proved implication is

    (∃h,L Ψ(r,h,L)) ⇒ η(r)=0.

The reverse remains unproved. Approximation by finite laws gives
∀ε>0 ∃h,L,x, not ∃h,L ∀ε>0 ∃x. Thus enumeration of accepted formats
is not a complete zero-gap procedure unless that missing coverage theorem
is supplied. Combining it with a positive-gap semidecision does not remove
this limitation.

The exact periodic caps already occur as
`sSup_range_quittingTerminalPayoff_update_eq_periodicWindow` and
`sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile` in
`UniformEquilibrium/Quitting/Cycles/PeriodicWindowEvaluation.lean` and
`PeriodicRootResponseSystem.lean`. The rational finite-profile verifier
and finite-clock approximation ingredients are also existing. The additional
assembly is the decidable fixed-format **all-accuracy** sentence with its
terminating finite-law compiler. The remaining mathematical question is
whether such fixed formats cover all zero-gap tables.
