# Finite-menu punishment completion and early-absorption characterization

Authors: external proof preserved in the [durable completion note](../notes/CODEX_ROOT__FINITE_MENU_PUNISHMENT_COMPLETION.md)
(punishment convergence and completion); CODEX_SKEPTIC (positive-singleton
necessity, direct reduction, and assembly).

Independent whole-packet reviews:
[CODEX_RENY](../feedback/CODEX_SKEPTIC__FINITE_MENU_PUNISHMENT_COMPLETION_DRAFT__BY_CODEX_RENY.md)
and [CODEX_HILBERT](../feedback/CODEX_SKEPTIC__FINITE_MENU_PUNISHMENT_COMPLETION_DRAFT__BY_CODEX_HILBERT.md).
Both passed the complete mathematical packet with no unresolved objection.
The assembler is not counted as a final reviewer.

## Exact statement

Fix a finite nonempty player set I and real terminal rewards rᵢ(S), for
i∈I and nonempty S⊆I. The first nonempty set of simultaneous quitters
ends the game; infinite all-Continue pays zero. All prescribed and deviating
strategies use independent private randomization, without a public signal
or an external correlating device. A unilateral deviation can replace its
player's complete behavioral strategy.

Let M≥0 bound every |rᵢ(S)|. Let Pᵢ be player i's unrestricted behavioral
punishment value, and let mᵢ(H) be its punishment value when both the
opponents and the responder use the finite menu

    F_H={0,…,H−1,Never},     F_0={Never}.

Let Bᵢ(p) and Uᵢ(p) be its full response cap and prescribed terminal payoff,
E(p)=maxᵢ(Bᵢ(p)−Uᵢ(p)), and

    ω(H)=maxᵢ(Pᵢ−mᵢ(H))₊.

Here x₊=max(x,0). Complete definitions appear below.

**1. Finite-menu punishment convergence.** For every i,

    mᵢ(H)→Pᵢ as H→∞,     and consequently ω(H)→0.   (1)

**2. Quantitative same-prefix completion.** Let N,H be integers with
N≥H≥1, let e≥0 and ρ>0, and let p be an actual independent product law
on F_N that is e-Nash against its displayed finite menu. Write Rₚ(t) for
the probability that all players survive before date t. If

    Rₚ(N−H)<ρ,

then for every η>0 there is an actual behavioral profile p̂ agreeing with
p before date N−H and satisfying

    E(p̂)≤e+2Mρ+max{2M√ρ, ω(H)+η}.                 (2)

One punishment target is selected before play. No reward-sign or
positive-singleton assumption is imposed in statements 1 and 2.

**3. Generic finite-game reduction and equivalence.** Define EA(r) to mean

    for every e>0, integer H≥1, ρ>0, and integer N₀≥0,
    there exist an integer N≥max(H,N₀) and a product law p on F_N
    such that p is finite-menu e-Nash and Rₚ(N−H)<ρ.  (EA)

For every finite nonempty quitting game,

    EA(r) implies existence of a uniform-equilibrium payoff.

If some own singleton reward sⱼ=rⱼ({j}) is strictly positive, the converse
also holds. Thus on that precisely defined class,

    UE(r) if and only if EA(r).                     (3)

The positive-singleton assumption belongs only to necessity and equivalence,
not to punishment convergence, completion, or the implication EA⇒UE.

## Conjecture-facing change

The “Alternative finite-game producer” in the named question
`FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER`
asks for EA on four-player tables with a positive singleton. This packet
provides its direct actual-data adapter to the terminal semantic endpoint
and proves the converse, for any finite nonempty player set. It does not
produce the sources requested by that question and does not close it.

The source requirements are strictly weaker than a small-full-regret
finite-clock source: only the displayed finite Nash comparisons and early
joint reach are requested. The source's own unrestricted regret can stay
equal to 1/2 even with zero finite-menu error and zero early reach for
arbitrarily long remaining windows; the exact example below proves this.
The missing full-response continuation is constructed by (2), not assumed.

The closest existing switching compilers instead require an exact
Nash–Bellman prefix at a supplied diagonal closed-tail endpoint, or a
normal support/ledger/floor switch object. The present reduction asks the
finite producer for none of those data. The finite-menu punishment limit
internally supplies the comparison needed by the exceptional deleted clock.

This is a strict weaker-source reduction with a semantic consumer, not a
new arbitrary-game producer. Its distinction from the earlier unconsumed
robust final-window restriction is explicit: that restriction supplies
positive reach under no UE but does not lower full regret. The present
completion consumes *small* reach; it neither repairs every positive-reach
final window nor supplies a source violating the robust restriction.

The qualitative Fin4 equivalence was already implied by the conference's
reviewed robust-window theorem and positive-singleton converse. The new
content claimed here is the explicit finite-source completion and its direct
any-finite-player reduction, not rediscovery of that Fin4 logical equivalence.

## Definitions and assumptions

Dates are nonnegative integers. Each player chooses Continue or Quit while
the game is live. If the first quitting date is T<∞ and its quitting set
is S, terminal payoff is r(S). If T=∞ it is zero. In the associated
stochastic game, stage payoff is zero while live and the selected terminal
reward in the absorbing state. A uniform-equilibrium payoff is one fixed
vector v such that for every ε>0 some behavioral profile and some horizon
threshold work at every larger finite horizon: that profile is ε-Nash for
expected average payoff and its payoff vector is within ε of v.

Before absorption the only public history is the all-Continue history.
Hence a player's behavioral strategy is specified, for payoff purposes,
by a sequence of private quit hazards. Equivalently it specifies a law on
Ω=ℕ∪{Never}. Given a law μ, its hazard at k is

    μ({k}) / μ({k,k+1,…,Never})

when the denominator is positive, and may be set to zero otherwise.
Conversely, multiplying the successive Continue probabilities gives the
finite atoms and their residual Never mass. Independently sampling these
laws reproduces the behavioral outcome distribution. The same description
applies to an unrestricted unilateral behavioral deviation. Behavior after
absorption is irrelevant and may be retained unchanged.

For a product law p=(pᵢ)ᵢ∈I, define

    Uᵢ(p)=Eₚ[ rᵢ(S) on finite absorption; 0 otherwise ],
    Bᵢ(p)=sup_ν Uᵢ(ν,p₋ᵢ),
    dᵢ(p)=Bᵢ(p)−Uᵢ(p),       E(p)=maxᵢdᵢ(p).

The supremum is over every law ν on Ω. Payoff is affine in ν, so Bᵢ(p)
is also the supremum of the deterministic finite quit-date and Never
payoffs. All these payoffs and caps lie in [-M,M], and dᵢ(p)≥0 because
retaining pᵢ is an available deviation.

For a product law on F_N, define its displayed cap by

    Bᵢᴺ(p)=max_{a∈F_N} Uᵢ(a,p₋ᵢ).

It is finite-menu e-Nash when Bᵢᴺ(p)≤Uᵢ(p)+e for every i. Because of
affinity, this is exactly Nash to error e against all mixed laws on F_N.
It says nothing about an omitted date N or any later date.

The punishment values are

    Pᵢ=inf_{v₋ᵢ product laws on Ω} sup_{a∈Ω} Uᵢ(a,v₋ᵢ),
    mᵢ(H)=min_{v₋ᵢ product laws on F_H} max_{a∈F_H} Uᵢ(a,v₋ᵢ).

The finite minimum exists: its domain is a finite product of compact
probability simplexes, and its objective is a finite maximum of continuous
functions. The infinite infimum need not be attained. It is finite, and
for every η>0 there is an actual opponent plan with cap below Pᵢ+η.

For t≥0, put

    aᵢ(t)=pᵢ({t,t+1,…,Never}),
    Rₚ(t)=∏ᵢaᵢ(t),       Dᵢ(t)=∏ⱼ≠ᵢaⱼ(t),
    A(p)=∏ᵢpᵢ({Never}).

Empty opponent products equal one. R is prescribed joint reach; Dᵢ is
reach with player i deleted. They are different probability modes.

Agreement before t in (2) means equality of all pre-t live hazards, using
any fixed completion of the source's zero-survival hazards. The output
also retains the source's irrelevant pre-t absorbed-history behavior if
a complete behavioral representative has been supplied.

## Source correspondence

The exact existing declarations below were read under their stated imports;
no new Lean file or build is claimed by this packet.

1. `quittingBestReplyValue`, `quittingPunishmentValue`,
   `quittingPunishmentValue_eq_stationaryPunishmentValue`, and
   `quittingStationaryUnilateralCap_eq_max_div` in
   `UniformEquilibrium/Quitting/Stationary/MinMax.lean` give the full
   behavioral punishment semantics and its existing stationary equality.
   `exists_quittingStationaryPunishmentRoot_lt_add` in
   `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` supplies
   an actual near-minimizing punishment row. Neither equality nor that
   near-minimizer construction is claimed as new.
2. `quittingOpponentSurvivalWeight_mul_le_jointSurvivalWeight` in
   `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTailSelection.lean`
   already gives the exceptional-clock inequality used below.
   `exists_phaseSwitchProfile_isεAsymptoticNash_of_diagonalJointSurvival`
   in `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTail.lean`
   assumes exact prefix Nash/Bellman matching and a diagonal family of
   target-closed tails. It does not have the finite-menu source of (2).
3. `exists_isεAsymptoticNash_of_normalSupportDelayedSwitch` and
   `exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing` in
   `UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`
   consume support/ledger/floor data or a normal sequentially perfect
   absorbing source. No such source is assumed or produced here.
   `QuittingRootSequenceLateSureSoloCompletion` in
   `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletion.lean`
   starts with unrestricted root-sequence Nash and deleted late-tail
   control, not merely finite-menu Nash.
4. `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
   in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`
   is the existing late-quit identity. The maximum-error Never consequence
   `singletonReward_le_nashError_div_never` in
   `UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`
   requires actual unrestricted root-sequence Nash; it is not applied to
   the finite-menu input of (2).
5. `stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead` in
   `UniformEquilibrium/Quitting/Paths/StoppingLawFiniteTail.lean`,
   `exists_finset_pmfFiniteComplementMass_lt` in
   `MathUE/ProbabilityMassFunction/DiscreteTightness.lean`, and
   `pmfTV_quittingCounterfactualOutcomeLaw_update_le` in
   `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`
   supply the existing discrete-law and total-variation interfaces.
6. `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
   in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
   is the semantic endpoint used in both directions of (3): terminal
   approximate Nash existence at every positive error is equivalent to
   existence of one fixed uniform-equilibrium payoff.

A bounded phrase/declaration search in these quitting subtrees found the
adjacent interfaces above, not the finite-menu punishment convergence and
arbitrary finite-menu completion asserted here. This is a repository
correspondence audit, not a claim of exhaustive literature priority.

The original [Solan–Vieille, “Quitting Games” (2001)](https://www.math.tau.ac.il/~eilons/quitting19.pdf)
was inspected at Section 1, Theorem 1.2, Propositions 2.4/2.6 and their
Section 2.5 context, and Section 2.6. Its model has zero nontermination
payoff and independent time-indexed strategies. Its main existence theorem
uses normalized positive own singleton rewards and a joint-exit payoff
restriction; its support-perfect absorbing-sequence argument is not the
finite-menu input of (2). Section 2.6 treats uniformity. We use the named
checked semantic endpoint instead of importing a paper-level uniformity
claim. The correspondence file is `Literature/SolanAndVieille2001.lean`;
that literature lane is not a built source of new theorem truth.

## Proof

### A. Scalar recursion and punishment convergence

Fix a player i. For y∈[0,1]^(I∖{i}), interpreted as the opponents' quit
probabilities at one date, set

    p_y(S)=∏ⱼ∈S yⱼ ∏ⱼ∈I∖({i}∪S)(1−yⱼ),
    Q(y)=Σ_{S⊆I∖{i}} p_y(S) rᵢ(S∪{i}),
    A(y)=Σ_{∅≠S⊆I∖{i}} p_y(S) rᵢ(S),
    c(y)=p_y(∅),
    Φ(x)=min_y max{Q(y), A(y)+c(y)x}.

The minimizer exists because the root cube is compact and the displayed
function is continuous. The empty opponent cube in a one-player game
has one point; then Q=sᵢ, A=0, and c=1.

Splitting an H+1-date opponent law into its first root and conditional
surviving H-date law gives

    mᵢ(0)=0,        mᵢ(H+1)=Φ(mᵢ(H)).              (4)

Here is the minimization justification. Against a fixed first root and
suffix, the responder chooses immediate Quit or Continue followed by a
best response in the suffix. If that suffix cap is b, the latter gives A+cb.
Every conditional suffix cap is at least mᵢ(H), proving the lower bound
in (4). Conversely choose a finite opponent suffix attaining mᵢ(H) and
a first root minimizing Φ(mᵢ(H)); concatenate them independently player
by player. This attains the right side. When c=0, the unused suffix may
be chosen arbitrarily. No responding player's randomization is shared
with opponents in this construction.

For x≤z, each root expression is nondecreasing in x, since 0≤c≤1;
the same holds for its minimum. Each root expression is 1-Lipschitz in
x, so taking minima preserves that bound. Also Φ maps [-M,M] into itself:
Q is an expected terminal reward, while A+cx is the expectation of a
reward in [-M,M] on absorption and x on no opponent absorption.

The iterates from zero are nondecreasing if Φ(0)≥0 and nonincreasing if
Φ(0)≤0, by monotonicity. They are bounded, so mᵢ(H) converges to some
ℓ∈[-M,M], and continuity gives Φ(ℓ)=ℓ. This permits either direction of
monotonicity and does not assume nonnegative rewards.

To show ℓ≤Pᵢ, fix any infinite independent opponent law v. Censor each
opponent's finite dates k≥H to Never, retaining its original Never atom,
and write b_H for the resulting finite-menu cap. Put

    θ_H=Σⱼ≠ᵢ Pr_v(H≤Tⱼ<∞).

Then θ_H→0 by countable additivity. Every pure reply k<H has exactly its
original payoff: it ends play by k if opponents have not already quit,
so their later atoms do not matter. The censored Never payoff differs
from the original Never payoff by at most 2Mθ_H, using the independent
coupling that moves only those late finite atoms. Thus

    b_H≤Bᵢ(v)+2Mθ_H.

Conversely b_H is eventually at least each fixed original finite-date
payoff, and its Never candidate converges to the original Never payoff.
Hence liminf b_H is at least the supremum over all original pure replies,
namely Bᵢ(v). We have proved b_H→Bᵢ(v), not merely pointwise convergence
of an uncontrolled changing test family. Since mᵢ(H)≤b_H, ℓ≤Bᵢ(v).
Taking the infimum over v proves ℓ≤Pᵢ.

For the reverse inequality fix x>ℓ. The fixed point and nonexpansiveness
give Φ(x)≤Φ(ℓ)+(x−ℓ)=x. Choose a minimizing root y; then

    Q(y)≤x,        A(y)+c(y)x≤x.                    (5)

If c(y)<1, repeat y independently at every date. The payoff of quitting
at date k is

    A(y)Σ_{h<k}c(y)^h+c(y)^kQ(y),

and Never gives A(y)/(1−c(y)). Finite quit payoffs interpolate between
Q(y) and A(y)/(1−c(y)); taking their supremum together with Never gives
the full cap max{Q(y),A(y)/(1−c(y))}. By (5) this is at most x, so Pᵢ≤x.

If c(y)=1, every opponent Continues, A(y)=0, and Q(y)=sᵢ. Equation (5)
implies sᵢ≤x. For x≥0, all-Never opponents have full cap max{sᵢ,0}≤x.
For x<0, the minimizing all-Continue root would force Φ(x)=max{sᵢ,x}=x.
Monotonicity would then give

    mᵢ(H)=Φᴴ(0)≥Φᴴ(x)=x

for every H, contradicting ℓ<x. Thus this last signed degenerate case
cannot occur. We have Pᵢ≤x for every x>ℓ, so Pᵢ≤ℓ. This proves
mᵢ(H)→Pᵢ. Finiteness of I proves (1).

### B. Quantitative same-prefix completion

Put t=N−H and abbreviate aⱼ=aⱼ(t), Dᵢ=Dᵢ(t), R=Rₚ(t). For distinct
players i,j,

    DᵢDⱼ=R∏ₖ≠ᵢ,ⱼaₖ≤R<ρ.                         (6)

At most one player can have Dᵢ>√ρ. If there is none, replace all
continuations from t onward by Never. If there is one, call it i_* and
choose a near-minimizing opponent punishment plan with full cap at most
Pᵢ_*+η. Append that plan at t, setting i_*'s prescribed tail to Never.
In both cases retain every pre-t live hazard. This defines the actual
profile p̂. Its target and all continuation prescriptions are fixed before
play. No observation of the identity of a deviator is required.

Under prescribed play the outcome can change only after joint survival
to t. Therefore for every player

    |Uᵢ(p̂)−Uᵢ(p)|≤2MR≤2Mρ.                       (7)

This uses non-strict inequalities also when M=0. We now bound complete
deviation caps against the old *finite-menu* caps.

For player i let Lᵢ be the expected payoff from opponents' first quit
before t when i continues throughout those dates, with zero contribution
when every opponent survives to t. Any pure quit date k<t has unchanged
payoff and belongs to F_N. Any later pure quit date or Never against p̂
has payoff at most Lᵢ+MDᵢ. Against the original p, the menu candidate
Never has payoff at least Lᵢ−MDᵢ. Thus, if Dᵢ≤√ρ,

    Bᵢ(p̂)≤Bᵢᴺ(p)+2MDᵢ≤Bᵢᴺ(p)+2M√ρ.             (8)

For the exceptional player Dᵢ_*>0. Its opponents' original laws,
conditioned on each opponent surviving to t, remain independent and,
after shifting by t, lie on F_H. No conditioning on i_*'s own survival
is needed; that survival may be zero. The best response against this
conditional opponent law is at least mᵢ_*(H). Its shifted pure response
is in F_N, so

    Bᵢ_*ᴺ(p)≥Lᵢ_*+Dᵢ_*mᵢ_*(H).                   (9)

Every new response continuing to t obtains at most
Lᵢ_*+Dᵢ_*(Pᵢ_*+η). Earlier responses are unchanged. Combining this
with (9), and using 0≤Dᵢ_*≤1, gives

    Bᵢ_*(p̂)≤Bᵢ_*ᴺ(p)+Dᵢ_*(Pᵢ_*+η−mᵢ_*(H))₊
            ≤Bᵢ_*ᴺ(p)+ω(H)+η.                     (10)

Every behavioral deviation has a stopping law and hence is a mixture of
these pure stopping payoffs. Therefore (8) and (10) bound unrestricted
behavioral caps, including adaptive strategies and arbitrarily late dates.
Subtract (7) from these cap bounds and use Bᵢᴺ(p)≤Uᵢ(p)+e. Taking the
maximum over players proves (2). There is no deadline or prefix-length
factor multiplying e.

### C. From early-absorption sources to one uniform payoff

Assume EA(r). Fix a terminal accuracy ε>0. Choose e=ε/4 and η=ε/8.
By (1), choose H≥1 with ω(H)<ε/8. Choose ρ>0 such that

    2Mρ<ε/4,        2M√ρ<ε/4.

These inequalities are automatic for M=0 and hold for sufficiently small
ρ otherwise. Apply EA at these e,H,ρ and N₀=1. Complete its actual
source by (2). The maximum in (2) is less than ε/4, and the joint-reach
term is less than ε/4. Thus E(p̂)<3ε/4<ε.

This constructs actual terminal approximate Nash profiles for every
positive accuracy. The established semantic endpoint stated in source
correspondence item 6 yields one fixed uniform-equilibrium payoff. The
selected profile may depend on ε; the final payoff target is fixed by
that endpoint. This proves EA⇒UE without any sign assumption.

### D. Positive-singleton necessity

Two elementary estimates are needed. First, for any actual profile and
any player j,

    dⱼ(p)≥sⱼA(p).                                  (11)

To prove (11), move only player j's original Never atom to a large finite
date k, leaving its originally finite atoms unchanged. This defines a
legal independent unilateral stopping law. On the all-Never event it
gains exactly sⱼ; when an opponent quits before k, or j was originally
finite, nothing changes. The remaining changed event is that j was Never
and the opponents' first finite quit is at least k. Its probability tends
to zero, excluding the all-opponents-Never event already counted. The
absolute error in the expected gain is at most 2M times this probability.
The deviation gains tend to sⱼA(p). Since dⱼ(p) bounds every such gain,
(11) follows without asserting cap attainment. If sⱼ>0, then

    A(p)≤E(p)/sⱼ.                                  (12)

Second, censor every player's finite atoms at dates k≥L to Never,
retaining its original Never mass; call the law pᴸ. Let θ_L be the sum
of moved marginal masses. For each fixed p, θ_L→0. The independent
coupling changes some coordinate with probability at most θ_L, so
prescribed payoff changes by at most 2Mθ_L. Against any fixed complete
unilateral deviation the opponent-only coupling gives the same bound,
uniformly over that deviation. Taking suprema preserves it for Bᵢ.
Consequently

    |E(pᴸ)−E(p)|≤4Mθ_L.                             (13)

Only late *finite* mass is moved. Neither original Never mass nor deleted
survival is asserted to vanish, and no uniform tightness of a family is
assumed.

Now assume UE and sⱼ>0. Fix e>0,H≥1,ρ>0,N₀≥0 and put

    b=min{e,sⱼρ}/2>0.

The semantic endpoint supplies an actual profile with E<b/2. Choose
its cutoff L≥1 so 4Mθ_L<b/2. By (13), E(pᴸ)<b<e. Applying (12) to
this truncated actual profile gives A(pᴸ)<ρ.

Finally choose N≥max{L+H,N₀}. All finite support of pᴸ lies before L,
so it is a legitimate product law on F_N. Its *full* regret below e
implies finite-menu e-Nash on this enlarged actual menu. As N−H≥L,

    Rₚᴸ(N−H)=A(pᴸ)<ρ.

This proves EA with its full quantifier order, and hence (3). The order
of choices prevents an invalid step: only a law with already-small full
regret is enlarged, never an arbitrary finite-menu Nash law.

## Boundary tests

### Negative rewards and one player

If a reviewed coordinate in a two-player game receives -1 at every
nonempty coalition, an opponent's sure date-zero quit forces cap -1.
Then m(0)=0 and m(H)=P=-1 for H≥1. The punishment iterates decrease;
nonnegativity or increasing convergence would be false here.

In a one-player game with singleton reward s, m(H)=P=max{s,0} for every
H≥1. The opponent product is empty and c=1 identically. This tests the
degenerate branch of the proof and does not require a second player.

For s=-1, Never is an exact uniform equilibrium. Every finite-menu
e-Nash law has total finite quitting probability at most e, so every
reach is at least 1−e. Choosing e=1/4 and ρ=1/2 makes EA impossible
for every H,N₀. Thus UE⇒EA fails without the positive-singleton
assumption. For s=1, sure Quit at zero is exact Nash and at any
N≥max{H+1,N₀} has R(N−H)=0, verifying the positive boundary.

The zero-reward game has M=0, P=m(H)=0, and E=0 for every profile;
there is no division by M in the completion theorem.

### Zero prescribed reach is not zero deleted reach

Consider two nontrivial clocks with rewards

    r({1})=(1,0),    r({2})=(2,0),    r({1,2})=(0,0).

“Two nontrivial clocks” does not mean two players with nontrivial own
strategic preferences: player 2's payoff coordinate is identically zero.
Let N≥2. Player 1 quits surely at zero, and player 2 chooses N−1 and
Never with probability 1/2 each. Player 1 receives 1. Its pure quitting
dates before N−1 give 1, quitting at N−1 gives 1/2, and Never gives 1.
Player 2 always receives zero. Thus the profile is exact finite-menu Nash.

At every t∈{1,…,N−1}, prescribed R(t)=0 but deleted D₁(t)=1. Quitting
at the omitted date N gives player 1 payoff 3/2. Its full regret is
exactly 1/2. The source cannot be extended unchanged on the strength of
its zero prescribed reach.

For any H≥1,e>0,ρ>0,N₀≥0, choose N≥max{H+1,N₀}. The same construction
passes the EA request while its own full regret remains 1/2. This is the
promised proper weakening of the source condition, not a global gap or a
four-active counterexample. Completion can instead make both prescribed
tails Never from the cut: player 1's original sure quit is retained, and
its new full cap is 1.

In the same table, m₁(1)=min_{q∈[0,1]}max{1−q,2q}=2/3, whereas P₁=1.
To see the latter, the existing stationary punishment characterization
gives cap 2 at every positive opponent hazard and cap 1 at the all-Never
opponent root. Thus the finite-window correction cannot simply be set
to zero at an arbitrary fixed H.

### Probability, information, and agency falsifiers

The proof never substitutes joint reach R for a deviator's deleted reach
Dᵢ. A zero-probability prescribed branch may have positive deleted reach;
it is precisely the exceptional branch in (9)–(10). Only opponents are
conditioned there, and Dᵢ>0 justifies that conditioning.

The fixed punishment target is not selected after learning who deviated.
The punishment need not be an equilibrium continuation: the theorem
asserts root terminal Nash, not subgame perfection. Deviations of the
other punishers are covered by their small deleted reaches and the 2M
payoff bound. Private randomization implements each appended opponent
law independently. There is no lottery over correlated whole profiles.

Every adaptive behavioral deviation before absorption induces a stopping
law on the unique all-Continue history. The pure-date/Never supremum
therefore controls the entire deviation, not merely one-stage deviations
or a bounded-memory class. Changing the game's information or correlation
structure would require a separate theorem.

## Adapter and consumer

From one actual finite source, the adapter is explicit at the mathematical
level: retain its pre-cut hazards, compute the deleted reaches, select the
possible exceptional player, and append one near-minimizing punishment
plan. The value convergence in (1) permits a sufficiently long requested
remaining menu before calling the source producer. The complete output
is the actual profile and bound (2), with no retained-target hypothesis.

From an all-request EA producer, Part C gives terminal approximate Nash
at every error, and the named terminal-to-uniform equivalence supplies
the fixed-payoff semantic consumer. Conversely Part D constructs EA
witnesses from UE under a positive singleton, by lawful finite truncation
before enlarging the displayed deadline.

If every sᵢ≤0, all-Never is already exact terminal Nash: any unilateral
finite quit gives only that player's singleton reward, and Never gives
zero. The same semantic endpoint yields UE. Thus the finite-quitting
conjecture reduces to establishing EA on positive-singleton tables. This
does not establish EA or give a finite decision procedure for it.

All new statements and proofs in this packet are ordinary mathematics.
Only the specifically named pre-existing declarations are attributed to
Lean; the packet does not claim checked implementation, integration, or
an arbitrary-game source construction.

## Lean handoff

Use the existing finite timing-menu realization and independent stopping-law
interfaces, without changing their game semantics. A narrow development
should provide the following theorem shapes, with names left to the
formalizer's local conventions:

1. Define mᵢ(H) from actual finite opponent product laws and the finite
   pure-response cap. Prove compact attainment, mᵢ(0)=0, and the scalar
   recursion (4). Prove monotonicity/nonexpansiveness of Φ, convergence,
   and equality of the limit with `quittingPunishmentValue`, retaining
   the negative x, c=1 argument and the uniform truncated-Never estimate.
2. At a supplied actual deadline-N finite-menu e-Nash law, prove the
   root-specific cap comparison (8) or (10) after a literal cut N−H.
   Reuse the deleted-clock product inequality and the existing actual
   near-optimal punishment construction. Return a behavioral profile
   preserving the prefix and satisfying (2). Do not place full regret,
   a closed-target equality, normality, or a punishment-compatible source
   tail in the input structure.
3. Define EA using only integer menus, independent laws, finite Nash, and
   actual reach. Compose the quantitative completion with
   `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`.
   Prove the converse with the existing Never/deviation and discrete-TV
   interfaces, preserving the order “full approximation, truncation,
   menu enlargement.”

Useful exact regressions are the one-player signs, the decreasing
negative punishment value, and the two-clock omitted-date example above.
The narrowest formal checks should compile only the new module and its
actual dependency closure, followed by the project-required trust checks.
No speculative refactor, source-code edit, or new implementation is part
of this packet's mathematical claim.

## Scope and nonclaims

- No arbitrary-game early-absorption producer, finite search decision
  procedure, effective convergence rate, or uniform deadline bound is
  proved. For real rewards no computational representation is assumed.
- EA requires every positive error e>0. Replacing this by an exact
  finite-menu Nash requirement e=0 is not claimed or used.
- The theorem does not prove UE for an otherwise unsolved table, settle
  the conjecture, answer the live Fin4 producer question, consume bounded
  exact capacity, or produce charged forward packets or renewable rank.
- The completed profile need not be finite-clock, completely absorbing,
  periodic, or subgame perfect. Deviations are nevertheless unrestricted.
- The same prefix, not the same tail or payoff target at each source
  tolerance, is retained. The final fixed uniform target comes only from
  the established all-error semantic endpoint.
- The packet is a direct weaker-source reduction. All-parameter EA is an
  infinite mathematical obligation; checking finitely many deadlines or
  finding one witness does not certify it.
