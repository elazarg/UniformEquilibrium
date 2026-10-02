# Fixed weighted sums of private successor-clock responses cannot certify a gap

Author: CODEX_TARSKI_PREMIUM. The response-law fixed-point strengthening was
suggested by ROOT; the elementary CDF realization is checked below.

Status: complete ordinary-mathematical obstruction to ONE fixed negative
certificate template, independently accepted by CODEX_NOETHER_SUPPORT in
[the preliminary review](../feedback/CODEX_TARSKI_PREMIUM__PRIVATE_SUCCESSOR_RESAMPLING_WEIGHTED_SUM_NO_GO__BY_CODEX_NOETHER_SUPPORT.md).
That review binds the mathematical body at SHA256
`23c771462c52fd43ca552e431cbd0a618495359c4692f59eeb12b45b11a639f9`;
only this status paragraph was subsequently updated. Internal retention
only: a response-law fixed-point corollary, not a named conjecture-branch
closure or export authorization. Not Lean-checked. A sixteen-
type exact finite witness already defeats the pointwise template. A direct
CDF construction also defeats its expected weighted sum for every bounded
reward table. No table with a positive all-behavior gap is found. No export,
Lean edit, generic checker, hierarchy, or experiment-system change is made.

## 1. Exact primitives, agency, and proposed certificate

There are four independent players I={0,1,2,3}. A table r assigns bounded
real rewards to every nonempty first-quitting coalition. Preabsorption and
Never pay zero. Write X=ℕ∪{∞}, with ∞ denoting Never and ∞+1=∞. A full
behavioral strategy is represented by its complete stopping law on X.

Against a prescribed product profile p, test these FOUR responses for i:

    D_i^Q = Quit at date zero,
    D_i^N = Never,
    D_i^m(p) = min_{j≠i} T'_j + 1,
    D_i^M(p) = max_{j≠i} T'_j + 1,

where the T'_j are privately sampled independent copies from the actual
opponents' laws p_j. These copies are independent of the actual opponent
clocks. The minimum is Never only if all copies are Never; the maximum is
Never if any copy is Never. The player preselects its own stopping time
using private randomness and never observes the actual opponent clocks.
Thus these are legal profile-dependent behavioral replacements, not a
correlated recommendation scheme.

The delay is genuine. If all three opponent laws put probability 1/2 on
zero and 1/2 on Never, D_i^m puts probability 7/8 on date one, and D_i^M
puts probability 1/8 there. Date one lies outside the opponents' displayed
finite menu. Their private finite draws can coincide with actual all-Never
opponents, so this is not an unshifted menu-preserving copier.

Fix nonnegative coefficients A_i,C_i,M_i,H_i for these four responses.
They may be chosen using the table but are fixed BEFORE the tested profile
or sampled clocks. Set W_i=A_i+C_i+M_i+H_i and define

    G_r(p)=Σ_i [ A_i gain_i(D_i^Q,p) + C_i gain_i(D_i^N,p)
                +M_i gain_i(D_i^m(p),p)+H_i gain_i(D_i^M(p),p) ].

If G_r(p)≥γ>0 held for every profile, then full terminal exploitability
would be at least γ/(Σ_i W_i), provided the denominator is positive.
The attempted finite certificate proves this expected inequality by a
pointwise lower bound on a symmetrized two-copy payoff expression over all
finite order/adjacency/Never types.

Theorem. For EVERY choice of the fixed nonnegative coefficients there is
one actual independent profile p*, depending only on those coefficients,
such that each player's weighted aggregate gain is zero for EVERY bounded
reward table. In particular G_r(p*)=0, so the proposed positive certificate
cannot exist. A finite sixteen-type obstruction to the pointwise proof is
also given below.

The conclusion is about the fixed WEIGHTED SUM. It does not say that all
individual tester gains are nonpositive or that their maximum cannot detect
a gain at p*. Profile-dependent weights, payoff-based tester selection, and
positive parts of expected gains are not covered.

## 2. Elementary construction of the actual response-mixture fixed point

For W_i>0 normalize the four coefficients to

    a_i=A_i/W_i,  c_i=C_i/W_i,  m_i=M_i/W_i,  h_i=H_i/W_i.

They are nonnegative and sum to one. If W_i=0, assign a_i=m_i=h_i=0,
c_i=1; the corresponding weighted-gain identity will be vacuous.

Define four sequences of finite stopping CDF values by

    F_i(−1)=0,
    F_i(n)=a_i
             +m_i[1−∏_{j≠i}(1−F_j(n−1))]
             +h_i∏_{j≠i}F_j(n−1)                 for n≥0.       (1)

The map on [0,1]^4 on the right of (1) is coordinatewise nondecreasing
and takes values between zero and a_i+m_i+h_i≤1. Starting from zero,
induction gives

    0≤F_i(n−1)≤F_i(n)≤1.

Hence ℓ_i=lim_n F_i(n) exists. Define a probability law p_i* on X by

    p_i*(0)=F_i(0)=a_i,
    p_i*(n)=F_i(n)−F_i(n−1)             for n≥1,
    p_i*(∞)=1−ℓ_i.

All masses are nonnegative and their total is one. Different players use
these laws independently. This is an actual profile, with possibly unbounded
finite support and positive Never mass, not a fictitious boundary clock.
The recursion computes numerical CDFs offline. It does not require recursive
sampling of actual opponents or couple different players' random draws.

For each n≥0, the CDF at n of D_i^m(p*) is

    1−∏_{j≠i}(1−F_j(n−1)),

and that of D_i^M(p*) is ∏_{j≠i}F_j(n−1). At n=0 both are zero, as
required by the strict one-date delay. Thus (1) states exactly that the CDF
of p_i* equals the CDF of the following mixture at EVERY finite date:

    p_i*=a_i δ_0+c_i δ_∞+m_i D_i^m(p*)+h_i D_i^M(p*).       (2)

Equality of all finite CDFs identifies all finite atoms; total probability
one identifies the Never atom too. Thus (2) is an equality of complete
stopping laws. No interchange of payoff limits or payoff-continuity argument
has been used.

Against fixed actual opponents, terminal payoff is affine in the player's
COMPLETE stopping law. Boundedness makes all expectations well-defined, and
private randomization realizes the finite mixture in (2). Multiplying its
payoff identity by W_i gives

    W_i U_i(p*)
      =A_i U_i(D_i^Q,p*_{−i})+C_i U_i(D_i^N,p*_{−i})
       +M_i U_i(D_i^m(p*),p*_{−i})+H_i U_i(D_i^M(p*),p*_{−i}).

Subtracting W_i U_i(p*) proves zero weighted aggregate gain for player i.
For W_i=0 the same assertion is 0=0. Summing proves the theorem, uniformly
over reward tables; p* did not depend on any reward entry.

## 3. A fully explicit equal-weight fixed point

If all four raw weights equal one for every player, the symmetric recursion
reduces to

    F(−1)=0,
    F(n)=f(F(n−1)),
    f(x)=1/4+3x/4−3x²/4+x³/2.

Here F(0)=1/4 and F(1)=51/128. The map is increasing on [0,1], fixes
1/2, and

    f(x)−x=(2x−1)(x²−x−1)/4>0            for 0≤x<1/2.

There is no other fixed point in [0,1/2]. Therefore F(n) increases to
1/2. The explicit law has finite atoms 1/4, 19/128, … and Never mass
exactly 1/2. Four independent copies of this law defeat the equal-weight
expected certificate for EVERY bounded table.

This law need not be Nash. For example, take r_i(S)=1 when i∈S and zero
otherwise. At this p*, player i's prescribed payoff is at most its finite
stopping mass 1/2, whereas Quit-now guarantees one. Thus an individual
tester has gain at least 1/2 even though the fixed weighted aggregate is
zero. Negative tester gains cancel it. The same table has an obvious exact
equilibrium with everyone quitting immediately.

## 4. Independent exact finite witness against pointwise symmetrization

Let T,T' be two independent copies of the full product stopping profile.
For the calculation of a SUM of expected unilateral gains, the private
copy used in each summand may be coupled with a common analytical vector T'.
This changes no summand's expectation and adds no device to the game.
Average the resulting payoff expression over arbitrary exchanges of T_j
with T'_j, for j∈I, to obtain a symmetrized expression. The independent
copy distribution is invariant under these exchanges.

Now restrict to the sixteen diagonal configurations

    T=T'=z^S,     z_i^S=0 if i∈S and ∞ otherwise,     S⊆I.

Every such configuration is itself a legitimate deterministic product law.
All copy exchanges fix it. At a diagonal configuration, BOTH successor-
resampling responses have the same payoff as Never:

- If some opponent quits at zero, any finite delayed response stops at one,
  after absorption; a Never response has the same payoff.
- If every opponent chooses Never, all its copies are Never and either
  resampling rule returns Never.

For a pure binary stopping profile z, let u_i(z) denote its terminal
payoff, with u_i(all Never)=0. Put B_i=C_i+M_i+H_i. The symmetrized
aggregate on the diagonal is therefore

    L(z)=Σ_i [A_i u_i(0,z_{−i})+B_i u_i(∞,z_{−i})
                     −(A_i+B_i)u_i(z)].                       (3)

Take independent binary probabilities θ_i=A_i/(A_i+B_i) whenever the
denominator is positive, and choose any θ_i otherwise. Averaging (3) over
z∈{0,∞}^4 with these probabilities gives EXACTLY zero: conditional on
z_{−i}, the two prescribed actions occur in the same proportions A_i,B_i
as the first two terms. Hence some diagonal type has L(z)≤0 for every
reward table and every choice of the fixed coefficients.

In particular a strictly positive pointwise lower bound is impossible. This
is a finite dual witness against those inequalities, not an assertion that
a mixture supported only on diagonal pairs is the law of two independent
nondegenerate profile copies. The actual-profile construction in Section 2
separately handles the expected certificate.

For unit raw weights the finite witness has integer coefficients. Write
u_i(S)=r_i(S) for S≠∅ and u_i(∅)=0. Then

    L(S)=Σ_i [u_i(S∪{i})+3u_i(S\{i})−4u_i(S)],

and the exact sixteen-term identity is

    Σ_{S⊆I} 3^(4−|S|) L(S)=0.                              (4)

Its nonnegative integer weights sum to 256. Expanding (4) cancels every
one of the sixty reward coefficients. Exact symbolic expansion independently
confirmed that zero identity and the polynomial factorization in Section 3.

## 5. Source audit and the precise boundary

The initial narrow search covered clock copying/resampling, private samples,
successor clocks, finite testers, and continuous response-operator fixed
points. The relevant existing obstruction is the finite-watchdog theorem,
restated in
`notes/CODEX_SPINOZA__FINITE_TESTER_SEPARATION_AND_TWO_ESCAPE_BOUNDARY.md`.
Its actual source declaration was read directly:

- `exists_quittingBehaviorProfile_forall_mem_finiteMenu_payoff_le` in
  `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdog.lean`.

That theorem concerns fixed finite menus of COMPLETE strategies. The delayed
resampling rules here are profile-dependent and genuinely escape such a
menu, so that theorem was not silently applied to their whole range. The
sixteen-type collapse and the law recursion above supply the needed separate
argument for the chosen fixed-weight template.

The exact mixture semantics were checked in:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`.
- `quittingBehaviorStoppingLaw_finiteStoppingLawMixture` and
  `quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect` in
  `UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`.

The related topological suggestion is consistent: successor (with ∞ fixed),
minimum, and maximum are continuous on the one-point compactification of ℕ.
Their pushforwards and finite mixtures give a continuous map on the compact
space of probability laws. But no fixed-point theorem or continuity of the
terminal payoff is needed: the monotone recursion (1) already constructs
the complete response-law fixed point and checks its Never mass.

Proved scope: fixed nonnegative weighted sums of the four displayed private
responses cannot give a positive all-law debt certificate, even in expected
form, and no pointwise two-copy proof of such a sum can work. Not proved:
that the maximum of these tester gains has zero infimum, that all continuous
or profile-selected response families are harmless, or that every Fin4 game
has uniform equilibrium. No extrapolation to discontinuous/state-selected
weights or general private resampling is made.

This exact fixed-weight mechanism is stopped. No table search, checker, or
larger response hierarchy is initiated after its finite and law-level
closure obstruction.
