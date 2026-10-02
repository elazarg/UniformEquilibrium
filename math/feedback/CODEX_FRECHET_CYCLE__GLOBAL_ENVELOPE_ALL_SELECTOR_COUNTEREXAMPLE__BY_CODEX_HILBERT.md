# Bounded independent check of the fixed-pivot global-envelope falsifier

Reviewer: CODEX_HILBERT. Verdict: mathematical PASS for the stated mechanism
counterexample; not an export gate or a claim against uniform equilibrium.

Reviewed the entire owned draft
`CODEX_FRECHET_CYCLE__GLOBAL_ENVELOPE_ALL_SELECTOR_COUNTEREXAMPLE.md`, SHA256
`3074a5b11159a135796193513a0a1080e055cb8bd1bf9ce24bccab76a137d040`.
Before reading its proof I derived the monotone pivot response and the
binding criterion directly from the full table, and identified the
zero-reach/first-active-date issue as the essential remaining test. The
draft's Sections4–5 resolve that issue correctly.

## Checked argument

For a finite pivot time t, the reward is exactly
F₀(t)=2−Pr(all opponents≥t). Since B_δ makes the pivot proper, its value
is1+Σ_k Pr(first opponent date=k)S₀(k+1). All coefficients are nonnegative.
Thus optimality binds S₀(k+1)=a^(k+1) precisely at every positive opponent
absorption atom. No conditional feasibility of B_δ is assumed.

At a reached date with q₁>0 and q₂=0, player1's comparison with Quit next
is q₀≥2q₀+(1−q₀)q₀(next). It implies both pivot hazards vanish, while
the binding constraint after the current opponent atom implies q₀(next)≥δ.
This contradiction is valid even before conditional suffix Nash has been
established: Quit next is one literal unrestricted response and its own
reward is the nonnegative predecessor indicator.

Similarly q₂>0 gives q₁≤q₀/(1+q₀)≤δ/(1+δ). The resulting q₁<1 and the
strict player1 comparison when q₂=1 exclude a sure player2. At inactive
dates a sure pivot would give player2−1 despite its available Quit payoff0.
These checks genuinely prove positive joint reach at every finite date
before the proof invokes conditional follower optimality. Dummy Never is
strictly optimal at each reached date because the pivot is proper.

The first-later-active-date argument is decisive. Starting from a tight
envelope date, any nonempty inactive stretch retains pivot survival at most
a, while player2's value at its first subsequent active date is at most
h=δ/(1+δ). Thus its current value is at most−1+a(1+h)<0. If there is no
later active date, proper pivot gives exactly−1. Both contradict a follower's
available nonnegative Quit payoff. Induction from S₀(0)=1 therefore proves
EVERY date active and the pivot law exactly geometric. This is not an
illicit import of the earlier daily-floor uniqueness argument.

The subsequent follower recurrence is the same literal equality already
checked in the earlier cyclic calculation, now legitimately after global
binding. Its backward contraction proves unique b,c. Stationary pivot
cap2 minus value2−δ/[1−(1−δ)(1−b)(1−c)] gives the stated loss and limit2/7.
The elementary bound c≤2δ for δ<1/2 is correct, so loss>1/4 is valid as
well. This lower bound is not needed for another constants campaign.

The alternative profile with only player1 geometric and every other player
Never is exact full Nash: its value (2,0,2,1) gives the nonowners their
global reward upper bounds, and player1 has identically zero payoff against
its three Never opponents. It belongs to the global-envelope domain when
the constrained proper owner is player1, not when it is pivot0. Thus the
claimed fixed-pivot all-selector failure is sound, and owner choice is a
genuine remaining distinction. The displayed homogeneous matrix witness
also correctly prevents attributing hard-residual coverage to this fixture.

No correction requested. I am separately testing selection across the four
possible one-owner domains, not enlarging this bounded review into a gate.
