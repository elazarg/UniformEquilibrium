# Actual-profile minimax barriers and root-graph deformation

Author: CODEX_TARSKI_PREMIUM.

Status: bounded endpoint/source test completed and STOPPED, after the stopped
[SAME-H mixture-cube test](../notes/CODEX_TARSKI_PREMIUM__SAME_POTENTIAL_OUTSIDE_FIBER_JOINT_LAW_TEST.md).
The elementary pointwise deformation observation below is proved, but no
global barrier lowering or new UE consumer is claimed. Section 4 gives an
exact finite-minimizer endpoint falsifier; §5 records the still-missing
positive-global-source implication. Endpoint retention
and the source origin of a uniformly active barrier remain open. No Lean
or export changes.

## 1. Why this is a different comparison

The earlier
[component return-cost test](../notes/CODEX_TARSKI_PREMIUM__GLOBAL_OUTSIDE_MINIMUM_AND_NASH_COMPONENT_RETURN_COST.md)
proved that a spanning Nash component cannot be read as a Bellman word:
the input annotation may rise in H along the component. That conclusion
is retained without change.

For a MAXIMUM-over-an-entire-profile-path objective, monotone parameter
travel is unnecessary. Each point can instead be independently prefixed
by its own exact root, and the maximum of the resulting full regrets is
bounded pointwise. This suggests a minimax deformation argument, not
chronological summation of H and not a new family of root annotations.

The table, actual behavioral interpretation, and SAME universal H are
those in the stopped test. Use X_N=∏_i Δ({0,…,N−1,Never}) and the
complete testers T_N={0,…,N,Never}. Let γ:[0,1]→X_N be a continuous
actual-profile path, allowing all four laws to move. Its actual payoff
path is u(t)=U(γ(t)).

## 2. The legal deformation observation

Let G_i(q,u)=Q_i(q)−A_i(q)−α_i(q)u_i. The continuous clipped map

    (t,q) ↦ clip(q+G(q,u(t)))

has exact root Nash profiles as its fixed points. Browder's theorem
gives a compact connected component D of the full root graph meeting
both parameter faces. The primary statement used is Theorem 1.1 of
Solan and Solan,
[Browder's Theorem through Brouwer's Fixed Point Theorem](https://arxiv.org/pdf/2107.02428).
It does not choose arbitrary prescribed endpoint roots and does not
by itself give a continuous section in t.

For (t,q)∈D, let P(t,q)=q⊕γ(t) be the actual independent prefix.
In clock coordinates its marginal has mass q_i at date zero, masses
(1−q_i)γ_i(t)(k) at dates k+1, and mass
(1−q_i)γ_i(t)(Never) at Never. This is a continuous map into X_(N+1).
Consequently P(D) is a compact connected actual-law set meeting some
root-prefixed endpoint profile on each side. It satisfies

    max_(p∈P(D)) E(p) ≤ max_(t∈[0,1]) E(γ(t)),          (1)
    H(U(P(t,q))) ≤ H(u(t))−a(q).                       (2)

Equation (1) uses the complete positive-part prefix cap identity at
EVERY graph point; (2) uses the SAME universal H at its actual payoff.
Both statements are pointwise. Parameter backtracking adds no cost to a
maximum and is not interpreted as a sequence of game transitions.
The extra played date and its extra late finite tester are retained.

If γ is semialgebraic, the finite root graph and its image are also
semialgebraic; one could use the usual semialgebraic connected-to-path
conversion. No such conversion is needed for (1)–(2), and this note
does not attribute path connectedness to Browder's general theorem.

## 3. The actual global minimax test, still open

The proposed consumer is not (1) alone. One would need an actual global
minimax barrier between two admissible endpoint sets, with the following
three facts derived at the same table rather than inserted as hypotheses:

1. The endpoint sets are retained by the selected spanning component.
   Even if both endpoints admit the zero root, that alone does not force
   a spanning component to use it. If every endpoint root is zero, the
   resulting endpoint is the COMMON SILENT SHIFT of the original profile,
   not literally the same stopping law. Its cap/payoff semantics agree
   when U≥s, but no connected low-regret interpolation to that shifted
   law is automatic.
2. A near-optimal barrier has its near-maximum-regret region in a compact
   set where every exact root has all player-deleted Continue factors
   at most κ<1. Then the pointwise cap identity lowers those high points
   uniformly. A positive joint absorption floor alone is insufficient:
   a solo active owner can have deleted Continue factor one.
3. The comparison survives the calendar enlargement X_N→X_(N+1), or a
   global all-calendar minimax level is defined with genuine endpoint
   stability. A fixed-N strict decrease by itself need not contradict
   anything, just as consecutive finite minimum values can decrease.

The SAME-H outside source provides exactly the two-active-root property
on its selected payoff fiber and a neighborhood, but it does not yet
force a GLOBAL path barrier to occur there. A barrier may instead remain
inside C⁺, where all Continue is an eligible zero-charge root. Thus one
cannot simply insert the outside fiber as the high part of an arbitrary
path and call (1) a strict minimax decrease.

Concrete next positive/negative test: for the all-calendar MAX-regret
connectivity problem between root-inert endpoint families, determine
whether the SAME H forces a positive barrier's high region to meet only
uniformly two-active-root payoffs, or forces an explicit root-inert
barrier point instead. This is a question about a GLOBAL optimizing path
family. An isolated exact-root calibration or a chosen nonoptimal path
would not settle it. Endpoint families and their shift closure must be
chosen before the minimax comparison, not retrofitted after the root
component is selected.

This observation does not currently furnish a new residual restriction:
no suitable endpoint families, positive barrier, or source-level active-
barrier alternative have been produced. It is the single next variational
question, not an asserted continuous Nash selector or a supplied-success
theorem awaiting only formatting.

## 4. Exact finite-minimizer endpoint test

The naive calendar entrance fails even when every choice is fixed by
uniqueness. This calibration has TWO players, original live/Never zero,
and literal rewards

    r({0})=(1,0),   r({1})=(2,−1),   r({0,1})=(0,1).

It is not claimed to carry the Fin4 SAME-H/no-UE source. Its purpose is
only to test the proposed finite-minimizer endpoint preservation.

On X₁, let a and b be the respective probabilities of Quit0, with the
remaining mass at Never. The full caps, including Quit1 and Never, are

    U₀=a+2b−3ab,           B₀=1+b,
    U₁=b(2a−1),           B₁=max(0,2a−1).

Thus d₀=1−a−b+3ab. For a≤1/2, d₁=b(1−2a); for a≥1/2,
d₁=(1−b)(2a−1). The GLOBAL full-objective minimum on X₁ is

    m₁=1/3, uniquely at (a,b)=(2/3,0).                  (3)

Here is a complete bound. For a≤1/3, d₀+d₁=1−a+ab≥2/3,
so the maximum is at least 1/3; the equality conditions cannot make
both debts 1/3. For 1/3≤a≤2/3, d₀≥1−a≥1/3, with equality
only at a=2/3,b=0. For a≥2/3, minimization in b balances the
increasing d₀ and decreasing d₁ at b=(3a−2)/(5a−2). The resulting
minimum is 2a(2a−1)/(5a−2), whose difference from 1/3 equals

    (3a−2)(4a−1)/(3(5a−2))≥0.

Again equality forces a=2/3,b=0. This proves (3) over all actual
independent laws in X₁, not a sampled set or finite-menu Nash set.

At the minimizer p, U=(2/3,0) and both debts are 1/3. The two
payoff-root differences at this actual continuation are

    G₀=(1−7q₁)/3,              G₁=2q₀−1.

All pure/boundary possibilities fail the corresponding signs. The UNIQUE
payoff-Nash root is q=(1/2,1/7). Its actual prefixed marginal laws are

    player 0: (date0, date1, Never)=(1/2,1/3,1/6),
    player 1: (date0, date1, Never)=(1/7,0,6/7).

Their full semantics are

    U'=(6/7,0),   B'=(8/7,1/6),   E'=2/7.              (4)

But a two-date competitor gives player 0 masses (1/2,1/4,1/4) on
those same dates and Never, with player 1 always Never. Its full payoff
is (3/4,0), full cap (1,0), and maximum regret 1/4. Hence

    m₂≤1/4<2/7.

EVERY Nash-prefix output from the unique X₁ minimizer is therefore
outside the X₂ minimizer set. The full tester values in (3)–(4) and the
competitor were independently enumerated with exact rational arithmetic,
including later finite dates and Never. This is not a bad-choice example.

The game is solved globally: player 0 quits geometrically with hazard
1/2 and player 1 uses Never. Player 0 gets and caps at 1; every finite
response of player 1 has conditional Quit payoff 2(1/2)−1=0 and its
Never response also pays 0. Thus the unrestricted terminal infimum is
zero. In particular this calibration does NOT refute endpoint invariance
at a genuinely positive GLOBAL minimum or an implication using the SAME
universal H. It rules out only the unproved finite-calendar entrance.

## 5. Positive-global source audit and stopping decision

If the unrestricted infimum m is actually attained, the set M of ALL
actual minimizers is closed under exact payoff-Nash prefixing: the cap
splice gives E'≤m and globality gives E'≥m. This elementary invariance
is valid, unlike its finite-calendar analogue in §4. It does not imply
that a chosen connected component or two chosen endpoint subsets of M
are separately preserved, nor that M is compact as an actual law set.

The current source guarantees a minimum only in the compact closure of
actual payoff/cap pairs. It does not make M nonempty by transporting
cap attainment through the finite PAYOFF realization theorem. Likewise,
minimizing H on that semantic minimum carrier gives the already known
root-inert source, not an actually attained endpoint family with a
nonzero topological barrier.

Even if actual attaining endpoints are separately supplied, the SAME-H
outside fiber does not currently produce two invariant endpoint classes,
prove a positive minimax barrier between them, or place the barrier's
high part in the uniformly two-active-root region. All of those are
global source statements, not consequences of the pointwise comparison
(1). No inference from a positive joint absorption floor to opponent
screening is used.

Decision: stop this bounded attempt with the exact missing implication:
produce actual shift-compatible invariant endpoint classes and a positive
all-calendar minimax barrier whose near-high part is uniformly opponent-
screened, from the SAME-H/positive-global-gap source. The current actual
outside theorem supplies screening only on its already off-minimum fiber;
it does not supply that variational placement. No such placement or
contradiction has been proved here, and §4 is not advertised as a
counterexample to that stronger hypothetical-global-source implication.
