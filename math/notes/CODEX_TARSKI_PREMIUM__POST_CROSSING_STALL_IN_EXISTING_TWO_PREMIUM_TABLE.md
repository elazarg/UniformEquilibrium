# The forced crossing does not yet supply a second positive root

Author: CODEX_TARSKI_PREMIUM.

Status: completed bounded exact test on HILBERT's EXISTING solved table,
not a new calibration family or export candidate. The incoming crossing
root is unique, and its strictly interior successor has ONLY all-Continue
as an exact root. The actual punishment vector equals the singleton vector
and has no sure Nash root. This does not realize a universal H certificate
or refute joint selection of a crossing word under that global hypothesis.

## 1. Existing table and exact operation being tested

Use the complete table from
[HILBERT's two-premium boundary](../notes/CODEX_HILBERT__TWO_PREMIUM_CORE_STATIONARY_AND_ROOT_CHOICE_BOUNDARY.md).
There are four players and zero Never. The first two coordinates depend
only on S∩{0,1}:

| Core pattern | r₀ | r₁ |
| --- | ---: | ---: |
| empty | 0 | 2 |
| {0} | 1 | −1 |
| {1} | 3 | 0 |
| {0,1} | 2 | 1 |

Set r₂(S)=0 if 2∈S; otherwise set it to −1 when the core pattern is
only {1}, and to 3 otherwise. Set r₃(S)=0 if 3∈S, and to 1 otherwise.
Thus |r|≤3 and s=(1,0,0,0). All own-quitting rewards are at least s_i,
so immediate Quit guarantees s_i against EVERY behavioral opponent law.
All-Never opponents give full cap s_i, proving the actual independent
punishment value P=s, not merely an assumed floor.

The question is the missing SECOND transition in
[the finite-word consequence](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_DRIFT_FINITE_WORD_FORCES_MACROSCOPIC_FLOOR_CROSSING.md):
does an absorbing exact root from below a singleton to strict domination
of every singleton, with normality and no sure root at P, yield another
positive exact root at its successor?

At v=(0,2,3,1), the existing note proves the unique exact root and successor

    q=(1/2,1/2,0,0),       w=F(q,v)=(3/2,1/2,2,1).         (1)

The root has a=3/4, collision mass 1/4, v₀<s₀, and w_i>s_i for all i.
Moreover min_i(w_i−s_i)=1/2>δa for every 0<δ≤1/4. It therefore meets the
strict floor-slack geometry of the crossing consequence. No H or low-H
co-realization is asserted on this solved table.

For completeness, player 3 strictly Continues at v. The exact core gains
are G₀=1−2q₁ and G₁=4q₀−2, independent of player 2. They have the unique
Nash pair q₀=q₁=1/2. At that pair, player 2's Continue payoff is 2>0,
so q₂=0. This verifies that (1) is not an arbitrary choice among good and
bad incoming roots.

## 2. Complete exact-root enumeration at the successor

Write an arbitrary successor root as (x,y,z,t). At w, player 3's Quit
endpoint is 0 and Continue endpoint is 1 for ALL other hazards, so t=0.
The remaining literal endpoint differences are

    G₀=Q₀−C₀=1−2y−(3/2)(1−y)(1−z),
    G₁=Q₁−C₁=2x−(1−x)(1/2+(3/2)z),
    C₂−Q₂=2+x−3y+3xy.                                    (2)

These are full finite product-root formulas at w, including every
same-date coalition; no stationary cap is substituted.

Suppose z>0 in an exact root. Then C₂−Q₂≤0. The case x=1 is impossible
because the last expression equals 3. Otherwise (2) implies

    y≥(2+x)/[3(1−x)]≥2/3.

The first expression is then at most 1−2y≤−1/3, forcing x=0. At x=0,
G₁=−1/2−(3/2)z<0, forcing y=0, a contradiction. Therefore z=0.
Now G₀=−(1+y)/2<0, so x=0; then G₁=−1/2<0, so y=0.

Thus EVERY exact root at w is all-Continue. Conversely all-Continue is
Nash because w≫s. This exhausts all zero, mixed and sure probabilities.
The crossing has no second positive exact transition at its actual
successor, even with unrestricted selection over its entire root set.

The same conclusion is locally robust in the relevant normalized sense.
Let e(q) be the maximum exact root regret at w. At small q, all Continue
endpoint margins stay uniformly positive, so e(q)/a(q) has a positive
lower bound for q≠0: some q_i≥a/4 and that owner's prescribed Quit mass
pays a fixed positive endpoint loss. Away from q=0, continuity and the
proved uniqueness give another positive lower bound on the compact set.
Hence inf_(q≠0)e(q)/a(q)>0. For sufficiently small robustness parameter,
even approximate-Nash eligibility has no positive-charge root at w.
No optimization of that parameter is needed or claimed.

## 3. The actual punishment root has no sure alternative

At P=s let the arbitrary root again be (x,y,z,t). Player 3 has

    G₃=−[1−(1−x)(1−y)(1−z)].

If t>0, exact Nash forces x=y=z=0. But then player 0 has G₀=t>0 and
cannot Continue surely. Therefore t=0 at every exact root at P.
The other gains are now

    G₀=z−y−yz,
    G₁=2x−2(1−x)z,
    G₂=−3x+y−xy.                                         (3)

If z=0 and x>0, G₀≥0 forces y=0, but then G₁=2x>0 is incompatible
with y=0. Thus x=0. If y>0, G₂=y>0 is incompatible with z=0, so y=0.

If z>0, G₂≥0 gives y(1−x)≥3x. If x=0, then G₁=−2z<0 forces y=0,
but G₀=z>0 forces x>0, impossible. Therefore x>0 and y>0, with x<1.
Their active endpoint inequalities give

    z≥y/(1−y),       z≤x/(1−x),

where y=1 is already excluded by G₀≥0. Hence y≤x. This contradicts
y≥3x/(1−x)>x. Thus this case is impossible as well.

Every exact Nash root at P is therefore all-Continue; in particular the
semantic sure-root alternative is absent. Normality or that no-sure
condition cannot repair the missing second transition in (1)–(2).

## 4. Honest stopping boundary

The existing table has a uniform-equilibrium payoff. HILBERT's note gives
the explicit safe lift of the checked three-player theorem: player 3 uses
Never, which pointwise weakly dominates its every other law because it
pays 1 if opponents absorb first and 0 whenever it quits first. The
other three players and all their behavioral deviations see exactly the
original three-player game. This does not contradict the absence of
stationary equilibrium also proved in that note.

In particular this test does NOT have a universal H. It refutes only the
specific proposed local implication from an exact crossing, strict floors,
positive collision mass, actual P=s and no sure root to a second positive
root. It does not refute a theorem retaining the full certificate and
jointly selecting among ALL crossing words from its minimizing face.

The current finite-word theorem must therefore stop at its stated
crossing. A useful further consumer needs either a genuinely global
selection among such words, or a justified change of the continuation
state which leaves this all-Continue basin. Repeating the crossing root
or merely requesting another equilibrium at w is not that operation.

The earlier strict-domination/unique-Continue note by FRECHET already
separated feasible payoffs from root existence. The present short check
uses HILBERT's existing EXACT incoming Nash root and adds the full
post-successor and actual-P root enumerations needed for this specific
finite-word test. No new fixture family or gate is proposed.

As an arithmetic check, independent exact outcome enumeration reproduced
all endpoint identities (2)–(3) on the 125 quarter-grid triples (x,y,z),
at BOTH w and P, and reproduced the four incoming endpoint pairs in (1).
The all-root conclusions use the inequalities above, not this finite grid.
