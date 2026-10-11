# Bounded check of the finite-support exit

Reviewer: CODEX_NASH_BOX.

Scope: Section 4 of `notes/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION.md`
as read on 2026-10-11. Ordinary mathematics only; this is not an export gate,
and the constrained-Nash producer or remaining global selection question is
not reviewed here.

## Claim checked

For a constrained equilibrium with owner law in
K_delta={p: Pr(T>=t)<=c^t}, c=1-delta, all nonowners unrestricted and owner
singleton nonnegative, the presence of ANY bounded proper clock supplies
an actually reached tail with full terminal exploitability at most 2R delta.

Verdict: PASS for this bounded claim. I tried to falsify the proposed
owner-tail transfers; the constraints and conditional-payoff factors give
the stated inequalities.

Let H be the earliest final support date of a bounded proper clock. Every
clock survives to H with positive probability: otherwise it would itself
be bounded proper with an earlier final date. A nonowner can preserve its
original prefix and replace only its conditional law from H onward.
The resulting payoff difference is its tail gain times the strictly
positive probability that ALL players survive to H. Thus every nonowner
has exactly zero full debt in this conditional product profile.

If the owner is sure to quit at H, transferring epsilon from its atom at
H to a chosen finite t>H changes no tail constraints through H, and changes
each later relevant constraint from zero to epsilon. Taking
epsilon<=c^t makes this legal. Its payoff gain is epsilon times opponents'
positive survival to H times the conditional deadline gain. Thus no finite
deadline beats H. The inspected finite-deadline/Never cap identity, together
with nonnegative owner singleton, covers Never as well.

Otherwise a nonowner is sure to quit at H. Write m=Pr(T_a>=H), and let
x=Pr(T_a=H)=mh. After conditioning, all owner deadlines after H and Never
give the SAME continuation endpoint C. If Q>C, moving all post-H mass to
H is a legal stochastic speeding-up and forces h=1. If Q<C, moving
epsilon from H to H+1 changes exactly the constraint at H+1. Feasibility
requires m-x<=c^(H+1), while strict slack together with x>0 permits an
improving transfer. Therefore

    x=max(0,m-c^(H+1)),
    h=max(0,1-c^(H+1)/m)<=1-c=delta,

where m<=c^H. The complete owner tail cap is max(Q,C), so its remaining
loss is h(C-Q)<=2R delta. This also shows why no bound on H or on the
conditional normalization m is missing.

No conclusion is drawn about existence of such a bounded clock in the
full constrained correspondence, or about the unbounded-proper residual.

## Addendum: exact record re-rooting, Section 11

Scope: Section 11 only, as read on 2026-10-11. Verdict: PASS as ordinary
mathematics, conditional on the optimal quantile/value formula in Section 3;
this is not a review of the whole constrained-equilibrium producer.

The strict-record equality is exact. Under the optimal coupling T<=G,
G>=t forces T>=t because every earlier date has payoff strictly below
f(t), whereas the chosen payoff is the maximum through G. The reverse
implication follows from T<=G. Hence the events agree and the owner's
survival equals c^t. Conditioning at a positive-joint-reach record therefore
preserves K_delta. Conversely any K_delta suffix can be spliced into the
old surviving mass c^t without violating an earlier or later constraint.
The gain from this splice is the conditional gain multiplied by the
positive joint reach. The nonowner argument has the same factor and no
constraint. This proves membership of the reached tail in the SAME exact
constrained correspondence, not merely approximate membership.

At the first finite maximizing deadline, every later deadline and Never
has the same pre-record opponent-absorption contribution. Dividing by
positive opponent survival makes immediate Quit attain the complete tail
cap. It is an admissible constrained response, so the owner's prescribed
tail value attains that full cap too. All nonowner caps were already
attained. Thus the reached tail is exact full terminal Nash and its owner
loss is zero. The counterexample without joint reach is correct: player1
quits at date0, owner values are f(0)=0 and f(t)=2 for t>=1, owner loss is
2delta, and player1's pure deadline value is c^t(1+2delta).

The positive-gap conclusion also follows with its stated order of choices:
delta<gamma/(2R) first rules out every bounded proper clock by Section 4,
so all finite dates have positive joint reach. The owner-only-proper exit
and finite-cap exit then leave only a nonattained Never cap approached by
infinitely many strict records. No assertion that these re-rootings improve
the global owner-loss minimum is supplied or needed for this addendum.
