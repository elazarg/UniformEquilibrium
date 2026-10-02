# One current candidate: exact zero at one escape-aware lower level

Identity: CODEX_RADO_BOUNDARY. Date: 2026-09-08.

Status: completed bounded exact feasibility test; selected lower query is
vacuous and the operation stops. No positive-gap certificate, η=0 proof,
new upper family, or export. The finite profile is obtained by truncating an
existing rational upper profile, not by a new strategy search. The hierarchy
is the existing sound all-behavior hierarchy, not a new relaxation language.

## 1. Candidate and finite test selected before calculation

The actual table is the unequal-high table in
[NOETHER's three-matching record](CODEX_NOETHER_SUPPORT__THREE_MATCHING_FAILURE_AND_UNEQUAL_HIGH_CYCLE_SYSTEM.md),
divided by four to lie in [−1,1]^60. For reproducibility, the following rows
are BEFORE division by four; masks use players 0,1,2,3.

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (2,2,1,1) |
| 02 | (8/5,1,1,0) |
| 03 | (1,0,1,2) |
| 12 | (0,1,8/5,1) |
| 13 | (1,2,0,1) |
| 23 | (1,1,2,2) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

The normalized table's canonical hash from the existing exact checker is
`5cda685b991381e2f2f56631bf78f138d497f43ce095cd793c8d060f92e88318`.
Live and Never payoffs are zero. All player clocks are private and
independent; every unilateral behavioral replacement is allowed.

Select the existing escape-aware level M=100000 and the lower query

    z∈R_M(r),     F(z)<γ,       γ=1/100000.              (1)

Here R_M is the existing cumulative quantile-clock outer set, not a set of
stationary or bounded-period profiles. An exact proof that (1) is infeasible
would imply γ≤η(r), covering ALL independent behavioral laws. The existing
single-shell checker uses the larger final shell N_M instead; proving its
lower bound γ would have the same all-profile consequence. We test both by
one literal feasible point. No alleged relaxed coalition law is realized
as a strategy.

Why this is not knowingly an already-solved candidate: the four tables in
the historical tracked campaign have different exact hashes and already
have complete alternating-pair upper families. Candidate C, C172, and the
displayed deadlock table likewise have later UE constructions. Those were
discarded during lookup. The current table above instead has only the
small-positive upper certificate in
[NOETHER's four-phase discovery](CODEX_NOETHER_SUPPORT__UNRESTRICTED_FOUR_PHASE_FULL_REGRET_DISCOVERY.md):
its normalized regret is between 1/32000 and 1/28000. This does not rule
out a true gap γ=1/100000. Neither failure of three matching grammars nor
the small-positive upper result is evidence that a positive gap exists.

## 2. Existing sound route and checker actually inspected

The definitions and literal all-profile lift were read in
[the maintained question](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md)
and the relevant statement/proof of
[the formalized quantile hierarchy](../formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md).
At level m the actual finite centers use dates 0,...,8m and Never, with
semantic radius 12/m. The objective is

    F(U,B)=max(0,max_i(B_i−U_i)).

Actual declarations inspected, under their imports:

- `finFourSingleShellLower` and
  `finFourSingleShell_quantitative_bracket` in
  `Research/Quitting/FinFourSingleShellOuter.lean`;
- `finFourSingleShellLower_le_exploitabilityInf` in the same file;
- the actual auxiliary-date, cap, and simplex encoding in
  `Research/Quitting/FinFourRationalSingleShellLower.lean`;
- `FinFourExactScaleCertificate.lower_verifies_infimum_sound`,
  `.lower_verifies_terminalGap`, and the no-uniform consumer in
  `Research/Quitting/FinFourIndependentCertificateSoundness.lean`.

Thus an independently accepted lower tree has an unrestricted semantic
meaning, not a supplied realization assumption. No Lean build or lower-tree
acceptance is claimed in this test.

For exact finite-law evaluation the experiment reuses `RationalLaw`,
`terminal_semantics`, and `ProfileCertificate.build`/`.verify` from
`Experiments/fin4_exact_search/fin4_exact_search/engine.py`, together with
`hazards_to_law` from its existing `direct_oracle.py`. The evaluator retains
all represented finite dates, one strictly after-support date, and Never.
Every later finite response has the after-support value. Arbitrary complete
behavioral responses average those pure-time values, so the cap is full.
The direct lower checker and its 24/m compression correction were also read;
no regional tree or restricted calendar bound was mistaken for a global one.

## 3. Exact actual center, including positive Never mass

Use precisely NOETHER's four rational product roots

    q = (1/10⁶) ·
        [283943  275040  293677  266055
         288138  279248  298184  270014
         297843  289542  308761  279333
              0       0       0       0].

Repeat them for FIVE cycles, at finite dates 0,...,19, and thereafter always
Continue. Each marginal has finite mass q_(t mod4,i) times its own previous
survival, and its remaining survival is the exact positive Never atom.
Their joint law is an independent product. This is a new literal truncation
of the already supplied profile, not public mixing among cycle outcomes.

The existing checker recomputes its full semantic pair a=(U,B) exactly and
accepts the strict upper target 1/25000. The exact result is

    1/32000 < E_r(p) < 1/25000.                         (2)

Every marginal's Never atom is positive; it was not replaced by a finite
late clock. Late Quit and Never remain different response tests. No
asymptotic truncation estimate is needed for (2).

## 4. Literal zero-objective point for the selected relaxation

Set v_i=(U_i+B_i)/2 and z=(v,v). This is a finite-dimensional semantic
point, not asserted to be the semantic pair of an actual strategy. Then

    F(z)=0,
    ‖z−a‖∞=E_r(p)/2<1/50000<12/100000.                (3)

For every m=3,...,100000 the same actual twenty-date center a is in
A_(8m+1), since 20≤25≤8m+1. Equation (3) puts z in its 12/m neighborhood.
For m=1 and m=2 use the actual all-Never profile as center instead. Its
payoffs are zero and its four full caps equal 1/4. The exact script checks
the required distances from z; the available radii are 12 and 6.

Hence z belongs to EVERY shell through M, and in particular the final
single shell. Since F is nonnegative,

    L_100000(r)=0,
    finFourSingleShellLower(r,100000)=0.                (4)

This is a genuine rational feasible witness to (1), not a positive-grid-gap
experiment. No sound lower certificate can prove a positive bound on either
of these two sets at this level.

## 5. Reproduction and stopping consequence

The complete bounded experiment is
[UNEQUAL_HIGH_SINGLE_LEVEL_FEASIBILITY.py](../experiments/CODEX_RADO_BOUNDARY__UNEQUAL_HIGH_SINGLE_LEVEL_FEASIBILITY.py).
Run from math:

```text
PYTHONDONTWRITEBYTECODE=1 python experiments/CODEX_RADO_BOUNDARY__UNEQUAL_HIGH_SINGLE_LEVEL_FEASIBILITY.py
```

It uses exact `Fraction` arithmetic, verifies the existing profile
certificate, checks the common midpoint and the two small-shell centers,
and prints the canonical table hash. It prints only and writes no files.
The compact symbolic padding argument avoids constructing the millions of
hazard variables at this hierarchy level. No general hierarchy implementation,
numerical optimizer, random table sweep, or new certificate format was used.

The selected negative test is therefore stopped as exactly vacuous at this
level. The same witnesses exclude a positive lower value at every earlier
level as well. Thus a positive certificate in this hierarchy would have to
use a level ABOVE 100000; that is only a necessary condition, not evidence
that any such certificate exists. The actual checked profile also gives
η(r)<1/25000, so a proposed original lower threshold at least 1/25000 is
already impossible. No stronger level prediction or search schedule is
asserted.

Equation (4) does NOT imply η(r)=0: a larger-level lower problem can
exclude this diagonal midpoint, and the actual center still has strictly
positive error. No all-accuracy upper sequence was produced. The precise
next requirement for any continued negative attack on this table is a
nonvacuous sound lower test beyond the present witness, not stationary
nonexistence or another bounded-calendar gap. This note does not launch
that further computation.
