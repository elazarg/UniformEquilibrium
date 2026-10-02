# Unrestricted four-phase full-regret discovery on the unequal-high table

Author: CODEX_NOETHER_SUPPORT.

Status: bounded numerical discovery plus one exact rational upper certificate.
No exact equilibrium, all-accuracy family, global minimum, or nonexistence
theorem was found. This is an internal calibration, not an export candidate.

## 1. Scope and actual result

The reward table is exactly the fifteen-row table in
[the preceding matching test](../notes/CODEX_NOETHER_SUPPORT__THREE_MATCHING_FAILURE_AND_UNEQUAL_HIGH_CYCLE_SYSTEM.md).
In particular its high directed cross rewards, in owner order (0,2,1,3),
are (8/5,8/5,2,2), with all opposite member rewards 1 and all within-member
rewards 2. Nothing in that table, including zero live/Never payoffs, changes.

All SIXTEEN Quit hazards q_(l,i) were free in [0,1], for phases l=0,1,2,3
and owners i=0,1,2,3. Product rows repeat with independent private choices.
The objective is the maximum unrestricted terminal deviation gain from
phase ZERO. It is not maximum one-stage defect, a squared indifference
residual, or the maximum over all suffix starting phases.

The strongest produced profile has the following rational Quit hazards:

    q = (1/10⁶) ·
        [283943  275040  293677  266055
         288138  279248  298184  270014
         297843  289542  308761  279333
              0       0       0       0].                (1)

Its actual full terminal exploitability E satisfies, by exact arithmetic,

    1/8000 < E < 1/7000.                                 (2)

The maximizing response is owner 1's literal Never strategy. Thus (1) is
explicitly NOT an exact terminal equilibrium. Its joint cycle survival is
strictly between 0 and 1/50; every opponent-deleted cycle survival is
strictly between 0 and 3/50. The exact payoff lies coordinatewise in (1,2),
approximately

    U=(1.08489667,1.12010511,1.07106911,1.13884691).

The selected mechanism is three dense rows with increasing hazards followed
by a silent row, not one of the earlier prescribed pair supports. The
strictly positive remaining error supplies no arbitrary-accuracy conclusion.

## 2. Complete response computation, including boundaries

For each phase l let R_(l,i) be the unconditional current absorption reward
to owner i and c_l the joint Continue probability. These are sums over ALL
sixteen product-row outcomes, with reward zero on the empty coalition.
Put C=∏_l c_l. When C<1 the literal initial prescribed value is

    U_i = [Σ_(l=0)^3 (∏_(h<l)c_h) R_(l,i)]/(1−C).        (3)

If C=1, every hazard is zero and actual prescribed payoff is zero.
This branch is treated as zero, not by assigning a nonzero formal Bellman
solution at the all-Never point.

For each owner and phase define Q_(l,i) as its current Quit expectation,
H_(l,i) as its current opponent-absorption expectation if it continues,
and d_(l,i) as all-opponent Continue probability. All opponent subsets
are included; in particular the full-table grand-coalition Quit term is
present. Let D_i=∏_l d_(l,i), and set

    L_(k,i)=Σ_(l<k)(∏_(h<l)d_(h,i))H_(l,i),
    P_(k,i)=∏_(h<k)d_(h,i),
    v_(k,i)=L_(k,i)+P_(k,i)Q_(k,i),        k=0,1,2,3.

If D_i<1, Never's ACTUAL payoff is

    N_i=L_(4,i)/(1−D_i).

The response that quits after n entire cycles and then at phase k pays

    N_i+D_i^n(v_(k,i)−N_i).                            (4)

Equation (4) proves that every later finite deadline is bounded by the
first four deadline values and Never. Conversely all five are actual
responses. If D_i=1, all opponent hazards are zero, so H=0, N_i=0, and
every finite Quit pays the own singleton 1. Hence in ALL boundary cases,

    B_i=max(v_(0,i),v_(1,i),v_(2,i),v_(3,i),N_i),
    E=max_i(B_i−U_i).                                  (5)

An unrestricted behavior strategy induces a distribution of its planned
first Quit time along the unique live history. Against fixed independent
opponents its payoff is the corresponding average of these pure response
payoffs. Therefore (5) is the full behavioral cap, not only a cap for
periodic deviations. Deleted survival tending to zero is checked directly
for (1), so no residual Never event is discarded in that certificate.

## 3. Reused checker and exact certificate

The reusable repository experiment
`Experiments/certsearch/block_pair/block_pair_periodic_probe.py` was read
completely, as was its imported `block_pair_stationary_certificate.py`.
The relevant evaluator functions are `cyclic_affine_values`,
`opponent_stage_values`, `stopping_choices`, `profile_values`, and
`full_stopping_gains`. They use `Fraction` arithmetic and require positive
deleted absorption. No external file was edited or executed as a main
program. The evaluator was imported read-only with bytecode writing disabled;
its terminal table was replaced only in that process's memory by the SAME
table being studied here.

The owned experiment is
[UNRESTRICTED_FOUR_PHASE_DISCOVERY.py](../experiments/CODEX_NOETHER_SUPPORT__UNRESTRICTED_FOUR_PHASE_DISCOVERY.py).
It stores the exact table, constructs (3)–(5) for discovery, and reuses the
repository evaluator for proper rational candidates. Reproduce (1),(2) with

```text
PYTHONDONTWRITEBYTECODE=1 python experiments/CODEX_NOETHER_SUPPORT__UNRESTRICTED_FOUR_PHASE_DISCOVERY.py --certificate-only
```

This command verifies every exact payoff recursion, all twenty phase-zero
pure-response gains (four deadlines plus Never for each owner), legal
probabilities, (2), joint survival below 1/50, and every deleted survival
below 3/50. The exact maximum printed by the rational checker is

    979155583877494122842122122982640014453337538472989963868815505254703358318558507470294190104525187942355582341106
    /7140358586473687576592038972458132121714255260573271004499826403642669100142237966486781140967677775411810754069670553.

Multiplication by 7000 and by 8000 verifies (2). Floating-point evaluation
of the SAME rational law agrees to the displayed precision; it is not
used to accept the strict inequalities.

## 4. Bounded discovery protocol

The numerical objective is a log-sum-exp approximation to the twenty gains
in (5) and an added zero label. At temperature τ its excess over E is
between zero and τ log 21. A projected inverse-BFGS iteration permits all
hazards to hit either boundary. Analytic derivatives of the response
formula were cross-checked against finite differences at a random interior
point. At zero absorption the values are literal but the code's zero
derivative is only an optimization convention: differentiability and even
continuity can fail there. Nothing in this experiment claims convergence
or global optimality of this algorithm.

The first bounded pass used six starts: the old eight-role profile, one
constant interior profile, two random complete profiles, all Never, and a
single sure-Quit profile. All sixteen coordinates remained free afterwards.
Its best result had E≈.000803861 and collapsed to one fully active row
separated by three silent rows. The all-Never start remained all Never;
this is not a local-minimum certificate.

A second pass used eight new complete random starts, with a lower initial
temperature to avoid washing all temporal variation into the same profile.
It found the three dense-row pattern leading to (1). Reproduction commands
from math/ are

```text
PYTHONDONTWRITEBYTECODE=1 python experiments/CODEX_NOETHER_SUPPORT__UNRESTRICTED_FOUR_PHASE_DISCOVERY.py --steps 160 --starts 6
PYTHONDONTWRITEBYTECODE=1 python experiments/CODEX_NOETHER_SUPPORT__UNRESTRICTED_FOUR_PHASE_DISCOVERY.py --random-pass --steps 180 --starts 8
```

Random seeds are fixed in the script. These are bounded upper searches;
their fourteen outputs do not cover the parameter cube. The exact rational
certificate (1) is retained independently of optimizer platform variability.

## 5. One attempted equality refinement and stopping boundary

The discovered near-silent row was set exactly to zero. A bounded Newton
attempt then used the twelve actually positive coordinates of the other
three rows to solve their twelve finite-response equalities v_(k,i)=U_i.
This was an attempt to identify a genuine equilibrium after discovery,
not a substitute objective for the original minimization.

The residual solve did not reach a legal zero. Its Jacobian condition
estimate grew from about 714 to about 6·10⁷ and the admissible residual
line search stopped. More importantly, its actual full regret increased
from about .0001373 to .0004330. Those candidates were rejected; a smaller
equation residual was not credited as a better equilibrium approximation.
No singularity or root-nonexistence theorem is inferred from that attempt.

The pass therefore establishes only the explicit legal full-regret upper
bound (2) and identifies a different dense-row mechanism. It does not
resolve whether support choice or period four is the remaining limitation.
No further period, support catalogue, or constant optimization is proposed.
The unsupplied next fact would be an actual zero or a vanishing-error
sequence for this table, not another supplied continuation certificate.
