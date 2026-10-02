# Same-profile singleton translation and finite-law approximation

Mathematics from the external FINITE_STOPPING submission, preserved by
CODEX_HILBERT. Ordinary corollaries of existing full-response affine and
censoring declarations; no new selector is constructed. The source was
reviewed at SHA-256
`7467beb21d9c16fd69a619272dd54f438af46372c293ab0f72a1955e638d10a8`;
see [the complete correspondence review](../feedback/FINITE_STOPPING__SOURCE_CORRESPONDENCE_BY_CODEX_RENY.md).

## 1. Exact full-debt translation

Let I be finite and nonempty. Independent laws on ℕ∪{Never} determine
the first stopping coalition; all Never pays zero. Rewards are bounded
but may have either sign. Write U_i, B_i, d_i=B_i−U_i for the actual
payoff, unrestricted behavioral cap, and debt of a profile p. Put
c=∏_j p_j(Never).

Suppose s_i=r_i({i})=0 and add a≥0 to every nonempty-coalition reward
of player i, still keeping Never zero. For the unchanged actual profile,

    B'_i=B_i+a,   U'_i=U_i+a(1−c),   d'_i=d_i+ac.     (1)

Proof: the pure finite-date response payoff f_i(t) tends, as t→∞, to
W_i+s_i D_i, where W_i is the Never response payoff and
D_i=∏_{j≠i}p_j(Never). With s_i≥0, Never adds nothing to the finite-date
supremum. Every finite response ensures absorption and hence gains exactly
a under the translation. The new singleton a is nonnegative, so its full
cap is also its finite-date supremum. The prescribed reward gains a only
on absorption, of probability 1−c. This proves (1), without attainment.

More generally d'_i=λ_i d_i+a_i c if λ_i>0 and both s_i≥0 and
λ_i s_i+a_i≥0. The sign restrictions cannot be dropped: a one-player
zero table at all-Never has zero debt, and changing its terminal payoff
to −1 still gives zero debt, not −1.

## 2. Canonical and all-ones tables on the same laws

For a four-player table r with own singletons (1,0,0,0), let R keep
player 0's rewards and add one to every nonpivot terminal coordinate.
Then R has all own singletons one, and for every unchanged profile,

    d₀^R=d₀^r,      d_i^R=d_i^r+c  (i≠0).             (2)

Moving only player 0's Never mass to a late finite date produces gains
converging to c, because its singleton is one. Therefore d₀^r≥c. With
E=max_i d_i, (2) proves the pointwise comparison

    E_r(p)≤E_R(p)≤2E_r(p).                             (3)

Every all-ones table arises by this construction. A global gap γ for R
gives a gap γ/2 for r; a gap γ for r gives at least γ for R. Positive
coordinate rescaling first reduces arbitrary strictly positive own
singletons to all ones; (3) is in those rescaled units.

The constant two can be attained. Let r₀(S)=1 always, let r₁(S)=1
when {0,1}⊆S and zero otherwise, and let r₂=r₃=0. Give player 0 half
Quit0 and half Never, with all others Never. Then

    c=1/2,  d^r=(1/2,1/2,0,0),  d^R=(1/2,1,1/2,1/2).

The bound c≤d₀ concerns joint Never, not the larger deleted probability
D₀. It cannot prove a small missing pivot cap before small regret exists.

## 3. Finite laws preserve full regret

For any actual profile p, move each player's finite mass at dates t≥N
to Never. Denote the resulting law by p^[N] and let
α_N=Σ_j p_j({N,N+1,…}), excluding literal Never. Then α_N→0.
If M bounds the rewards, independent coupling gives

    |U_i(p^[N])−U_i(p)|≤2Mα_N,
    |B_i(p^[N])−B_i(p)|≤2Mα_N,
    |E(p^[N])−E(p)|≤4Mα_N.                             (4)

For the cap comparison couple only the opponents, uniformly over every
replacement law. This includes ties, late dates, positive original Never
mass, and unbounded behavioral deviations. One may choose N above any
given lower bound.

For a canonical law on {0,…,N−1,Never}, let E_N be its menu regret,
W₀ its pivot Never value, and D₀ the opponents' joint Never probability.
The complete cap identity gives

    E_full=max{E_N, W₀+D₀−U₀}.                         (5)

Indeed every omitted finite pivot date gives W₀+D₀, while omitted
nonpivot dates equal their Never values. Thus all-accuracy finite laws
meeting both terms in (5) are equivalent to all-accuracy full behavioral
laws in the canonical table. Combining (3) and (4) gives the corresponding
equivalence for all-ones tables. No exact-menu Nash requirement is imposed.

The exact ingredients are already in
`Quitting/Punishment/FinitePureReplyValue.lean`,
`Quitting/Terminal/TerminalAffineReward.lean`,
`Quitting/Punishment/SinglePivotProfileDebtTransport.lean`,
`Quitting/Paths/LateFiniteStoppingLawCensor.lean`, and
`Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
The general signed-source normalization still needs its different
punishment-tail lift; (3) does not replace that theorem outside this
nonnegative-singleton subclass. The unresolved problem remains actual
selection of laws with both terms of (5) small.
