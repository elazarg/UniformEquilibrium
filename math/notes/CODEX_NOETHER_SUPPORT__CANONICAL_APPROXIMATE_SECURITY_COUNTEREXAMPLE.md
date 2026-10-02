# Canonical payoff security does not imply approximate better-reply security

Identity: CODEX_NOETHER_SUPPORT.

Status: the second and final condition checked in this literature route
fails on an exact solved canonical table. The fixture below is payoff
secure and has only one player with an own-response discontinuity at Never,
but is not approximately better-reply secure. It nevertheless has an exact
terminal equilibrium. This closes this attempted general use of the
Bich–Laraki criterion; it does not refute quitting-equilibrium existence.
Ordinary mathematics, not independently reviewed or Lean-checked. No export
is proposed.

This continues the
[marginal-continuity audit](CODEX_NOETHER_SUPPORT__SINGLE_PIVOT_MARGINAL_CONTINUITY_OBSTRUCTION.md).
The stopping-law spaces, topology, independence, complete behavioral
deviation domain, zero Never payoff, and source declarations are unchanged.

## One weaker theorem, stated with its actual quantifiers

The only additional primary result inspected is Bich–Laraki (2017),
Definition 3.11 and Theorem 3.12, printed page 90 of the
[same original paper](https://onlinelibrary.wiley.com/doi/pdf/10.3982/TE2081).
Let Γ be the closure of the actual payoff graph in X×ℝ^I. Let E be the
set of profiles x that are limits of actual ε_n-Nash profiles x^n with
ε_n→0 and with a convergent payoff subsequence. Their condition is

For every (x,v)∈Γ with x∉E, some player can secure strictly more than v_i.

The theorem gives approximate-equilibrium existence for compact quasiconcave
games satisfying this condition. It does not require global continuity of
best-response values. Its exception concerns the limiting profile x,
not whether this particular graph payoff v is an approximate-equilibrium
payoff at x.

Here a secure value uses one fixed own response throughout some neighborhood
of the specified opponents. Nonnegative own singletons imply that the
supremum of such values equals the actual unrestricted cap B_i, by the
finite-response continuity and late-Never identity proved in the preceding
note. Thus this game's condition becomes

For every (x,v)∈Γ with B_i(x_−i)≤v_i for all i, one must have x∈E.       (1)

Pointwise payoff security chooses the securing response after the opponents
are fixed. It supplies neither one response chosen uniformly over all
opponent profiles nor a continuous response selector. No interchange of
these quantifiers, and no uniform-payoff-security assertion, is made here.
Even the exact pointwise secure-cap equality does not establish (1).

## Complete canonical fixture and its solved equilibrium

Take two players 0 and 1 and the terminal table

| Quitting coalition S | r_0(S) | r_1(S) |
|---|---:|---:|
| {0} | 1 | 1 |
| {1} | 0 | 0 |
| {0,1} | 4 | 0 |

Own singletons are (1,0). All clocks are independently drawn from
ℕ∪{∞}. Player 1 is paid one exactly when player 0 quits strictly before
player 1 at a finite date; player 1 is paid zero whenever it participates
in the first quitting coalition. Consequently player 1's payoff is
continuous in its own law against every fixed opponent law. Player 0 is
the sole player with the possible positive own late-Quit/Never gap.

The profile (δ_0,δ_∞) is exact terminal Nash, with payoff (1,1). Player 0
gets at most its singleton one against Never, and player 1 gets at most
one, already obtained by Never. The same reasoning proves that
(δ_n,δ_∞) is exact terminal Nash for every finite n.

To obtain precisely four canonical players, add players 2 and 3 with zero
payoff at every outcome. For each nonempty S, let Q=S∩{0,1}; use the
displayed active coordinates if Q is nonempty and (0,0) if Q is empty.
This specifies all fifteen rows and gives singleton vector (1,0,0,0).
Both dummies choosing Never preserves every calculation below, and their
unrestricted caps are zero.

## Why all-Never alone is not the falsifier

At z=(δ_∞,δ_∞), caps are (1,0). The collision sequence (δ_n,δ_n) tends
to z with payoff (4,0), so nobody secures strictly above that graph payoff.
However z∈E: the exact equilibria (δ_n,δ_∞) also tend to z, with payoff
(1,1). The premise x∉E in the approximate-security condition therefore
does not hold at z. Declaring failure from the collision graph payoff at
all-Never alone would confuse a profile limit with a selected payoff limit.

## A genuine failure after a fixed finite prefix

Set

x_0=x_1=(1/4)δ_0+(3/4)δ_∞.

The exact prescribed payoff is U(x)=(7/16,3/16). Against x_1, player 0
gets 7/4 by quitting at date zero, 3/4 by quitting at any later finite
date, and zero by Never. Against x_0, player 1 gets zero by quitting at
date zero and 1/4 by every later finite date or Never. Thus

B(x)=(7/4,1/4).                                           (2)

For every integer n≥1, use the actual independent laws

x_0^n=(1/4)δ_0+(3/4)δ_n,
x_1^n=(1/4)δ_0+(3/8)δ_n+(3/8)δ_∞.

They converge weakly to x. The exact first-coalition probabilities are

| First coalition | Probability |
|---|---:|
| {0} | 3/16 + 9/32 = 15/32 |
| {1} | 3/16 = 6/32 |
| {0,1} | 1/16 + 9/32 = 11/32 |

The probabilities sum to one. Hence every n has the same payoff

U(x^n)=(59/32,15/32)=v,

and (x,v)∈Γ. Comparing with (2),

v_0−B_0(x_−0)=3/32>0,
v_1−B_1(x_−1)=7/32>0.                                    (3)

No player can secure strictly above v_i: even at the opponents x_−i
themselves, its unrestricted cap is smaller. The zero-payoff dummies
cannot secure above their graph payoff zero either.

It remains essential to prove x∉E, rather than merely showing these
particular x^n have regret. The following bound holds for every actual
profile μ, including arbitrary unbounded stopping laws:

d_1(μ)=B_1(μ_−1)−U_1(μ) ≥ μ_1({0}) μ_0({0}).             (4)

Indeed, player 1's date-zero payoff is always zero. Its date-one payoff
is exactly μ_0({0}), so B_1≥μ_0({0}). The complete own-law mixture
formula expresses d_1 as the integral of nonnegative cap slack over all
of player 1's pure clocks. Keeping just its date-zero atom gives (4).
For the four-player extension the date-one formula remains exact: if
player 0 quits at zero, adding dummy quitters does not change the active
reward; otherwise player 1 cannot earn one before its own date-one Quit.

The finite atom {0} is clopen. Therefore every profile sequence μ^k→x
has μ_0^k({0})→1/4 and μ_1^k({0})→1/4. Formula (4) gives

liminf_k d_1(μ^k) ≥ 1/16.                                (5)

This excludes every vanishing-error sequence approaching x, regardless
of its payoff limit. Thus x∉E. Equations (3) and (5) refute (1), so the
canonical game is not approximately better-reply secure.

## Exact failed implication and remaining scope

The failed implication is

compact independent law spaces + payoff security + own-law continuity for
all nonpivots ⇒ approximately better-reply secure.

The obstruction is a finite supported action with a persistent strict
loss. An escaping collision can lift the graph payoff above every cap
at the limit without eliminating that finite supported-action loss in
nearby actual profiles. The criterion must rule this out or repair it;
pointwise payoff security does neither.

This example does not assert that uniform payoff security fails, that
every Reny solution is unusable, or that no other argument could exploit
the canonical singleton structure. It proves that the selected weaker
theorem cannot apply to every raw canonical table solely from the supplied
conditions. The exact equilibrium above prevents interpreting it as an
obstruction to all-error independent-law existence.

No second paper, further existence criterion, new compactification,
equilibrium hypothesis, Lean file, or export was introduced. The relevant
actual-law mixture and finite-atom continuity declarations are already
listed in the preceding note. Next requested check: independently verify
the three coalition masses and the all-profile debt lower bound (4).
