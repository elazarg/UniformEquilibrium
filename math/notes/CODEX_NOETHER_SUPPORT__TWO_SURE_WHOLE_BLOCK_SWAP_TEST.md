# The two-sure whole-block swap: a retained pair bill and the remaining comparison

Author: CODEX_NOETHER_SUPPORT.

Status: bounded actual-operation test, ordinary mathematics. The high-pair-mass
arm provably cannot improve full regret. The complementary arm remains
unconsumed; no improving profile or global counterexample is claimed. This
is not an export proposal for another prefix ledger.

## 1. Source and actual operation

Use I={0,1,2,3}, signed unit-bounded rewards r, and Never payoff zero.
The actual source is an unpadded date-zero root: K={0,1} quit surely;
owner 2 quits with probability x and owner 3 with probability y, otherwise
Never, with 0<x,y<1. Assume its full unrestricted exploitability attains
the positive global minimum m. In the membership-stretch source, also
retain the original worst table r*, its value Ω≥m, the exact common
non-own-singleton stretch, freely reselected final own singletons, and
strict pure-coalition separation Γ_K>m. No normality is transferred to
this selected profile beyond the source's stated fields.

The operation moves the TWO optional clocks to date zero and the TWO
sure clocks to date one, retaining x,y and literal Never masses. This
is a product-law change of four private clocks, not an event-conditioned
exchange. Write w=(1−x)(1−y). Its prescribed payoff is

    V_i=w r_i(K)+x(1−y)r_i({2})+(1−x)y r_i({3})+xy r_i({2,3}). (1)

The whole-block exchange in
[FRECHET's earlier note](CODEX_FRECHET_CYCLE__CONTESTED_SINGLETON_BLOCK_EXCHANGE_BOUNDARY.md)
was checked first. Here the source really supplies the two disjoint
participation groups; there is no attempted exchange only on a selected
private event. The issue is the complete-cap comparison, not agency.

## 2. Every response is retained

For a sure owner h∈K define

    Q_h=w s_h+x(1−y)r_h({h,2})+(1−x)y r_h({h,3})
          +xy r_h({h,2,3}),
    L_h=r_h(K\{h})−r_h(K).

Its complete new debt is

    d'_h=max(0, Q_h−V_h, w L_h).                              (2)

Quit at zero gives Q_h. Quit at one gives its prescribed V_h. Every
later finite date and Never give V_h+w L_h, since the other sure owner
still quits at one. There is no discarded early or after-support test.

For optional i, write j for the other optional, z for i's Quit
probability, and v for j's. Put

    D_i=(1−v)s_i+v r_i({i,j})−v r_i({j})−(1−v)r_i(K),
    J_i=(1−v)[r_i(K∪{i})−r_i(K)].

Then the complete new debt is

    d'_i=max((1−z)D_i, −z D_i, J_i−z D_i).                   (3)

The three rows are respectively Quit at zero, Never (equally every
finite date after one), and Quit at ONE. In particular the sure-date
joining response is a new full tester, even though i's prescribed law
puts no mass there. Omitting it gives a false favorable comparison.

All randomized behavioral responses are bounded by these pure-clock
maxima. The two source sure clocks ensure absorption under every
single-player deviation, so no unlisted tail value is being presumed.

## 3. A source-level arm that the swap cannot consume

For z∈[0,1], the maximum in (3) is at least
(1−z) max(J_i,0). For J_i≥0 this follows by taking the convex
combination with weights z and 1−z of its first and third rows:

    z[(1−z)D_i]+(1−z)[J_i−zD_i]=(1−z)J_i.

For J_i<0 it follows from nonnegativity of debt. This is a proof
combination of scalar bounds, not a correlated strategy.

Let Γ_K be the full pure date-zero coalition K's regret, namely the
maximum of zero, L_0,L_1, and the two optional joining gains
r_i(K∪{i})−r_i(K). Equations (2)–(3) give the exact universal lower bound

    E_swap ≥ w Γ_K.                                          (4)

Thus at the actual strict-separation source this move cannot improve
whenever w Γ_K≥m. This does not exclude the source or settle the
conjecture: it rules out this specified competitor in that arm. The
source's strict Γ_K>m does not itself imply w Γ_K≥m.

## 4. Low pair mass: the original-table comparison is not automatic

For w Γ_K<m, (4) is not an upper estimate and gives no improvement.
The remaining rows in (2)–(3) involve all newly exposed optional-only
and one-sure/optional coalitions. They are actual outcomes or actual
counterfactual outcomes; their absence from the old prescribed support
does not remove them.

There is also an exact difference from the frozen inverse-stretch
argument. At its original simultaneous root, at least two sure owners
screened every own-singleton coordinate from every full response.
After this swap, even a sure owner can obtain its singleton by quitting
at the new date zero.

To isolate the issue, hold the 56 non-own-singleton coordinates fixed
and change only s_i by Δ_i. Each sure owner's early gain in (2) changes
by w Δ_i; its other rows are unchanged. For an optional i, the early
gain in (3) changes by w Δ_i, whereas BOTH its Never and sure-date
gains change by −z(1−v)Δ_i. These opposite signs are exact.

Consequently the source's arbitrary re-selection of the four own
singletons cannot be suppressed when evaluating this new profile at
r versus r*. Even separating the inverse stretch of the other 56
coordinates leaves these signed terms. Original globality says
E_(r*)(swap)≥Ω; final globality says E_r(swap)≥m. To contradict either,
one still needs a valid upper comparison at that same table. Neither
the unchanged old root nor singleton-fiber maximality supplies it.

The bound (4) consumes the proposed operation in its high-w arm.
For the other arm this test has not obtained a source-forced sign for
the remaining complete rows. No additional solved-table trap is used
as a substitute for the genuine global hypotheses.

## 5. Exact verification and next boundary

Direct enumeration of all stopping responses 0,1,2,Never checked
(1)–(4) on 540 rational signed-table/profile cases: 60 deterministic
unit-cube tables and x,y∈{1/4,1/2,3/4}. All identities and the pair
floor passed exactly with rational arithmetic. Zero tested tables are
claimed to realize the positive-global-minimum source.

The source and complete pure-coalition convention are those in the
frozen [membership-stretch reduction](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md)
and [three-sure packet](../exports/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md).
No Lean implementation or export edit was made.

Next question: can a SAME-table global source restriction bound the
low-w arm's actual optional-only rewards and all rows (2)–(3), or is
a different finite move required? Do not replace this question by
another unsigned block-commutator or a lower-bound-only compiler.
