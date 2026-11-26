# Independent review of the constrained critical-face exclusion

Reviewer: CODEX_CRITICAL_REVIEW.

Verdict: **MATHEMATICAL PASS for the exact theorem in Sections 1–6.**
There is no unresolved mathematical objection to the exclusion of
`B_h=m` at every constrained minimum, or to the resulting unique
AllContinue root at the critical reduced continuation. This is ordinary
mathematics, not a Lean verification. Keep the result internal for now:
it refines a source normal form but does not yet provide a new raw-table
existence class or consume the surviving constrained minimum.

Reviewed source:
[CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_BARRIER.md](../notes/CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_BARRIER.md).

Source SHA256:
`5887a9fc82463a883846f37eafd8904b09148a40f614ac2fceccf5f5485ce4e5`.

Checker SHA256:
`f6c79d81827e9e14584a93c65d403eb463b350a54db1588eec486c45e2abae20`.

## Exact claim reviewed

The finite native quitting table has four players, own singleton rewards
zero, and zero live and AllNever payoff. Its unrestricted independent
complete stopping-law semantics supplies the compact augmented carrier
`H=closure{(U,B,N,e)}`. In particular, `B` is the supremum over every
finite-date and Never response, and `N` retains the original Never
probabilities, rather than being recomputed from a weak limit of clocks.
Write

```text
d_i=B_i-U_i,        nu=product_i N_i,
A=inf{sum_i d_i(P): P actual and nu(P)=0}.
```

Assume `A>0`. For any distinguished player `h` and `0<r<A`, put

```text
C={Y in H: d_i(Y)=0 for i!=h},
J_r=d_h+r nu,       m=min_C J_r.
```

The theorem says that **every** minimizer in `C` has

```text
B_i=U_i>=0 (i!=h),       B_h>m,       U_h>r nu.
```

At its continuation `w=B-m e_h`, every exact finite product Nash root is
AllContinue. The point need not be an actual-law profile. No continuous
selection, finite calendar, response attainer, inverse-column condition,
or original all-END assumption is used.

## Carrier and source checks

The actual complete-law cap equals the unrestricted behavioral cap:
before absorption there is one live history at each date, so a complete
behavioral response is represented by its first-Quit distribution, and
its value averages the pure-date and pure-Never values. Independence
across players is preserved by prefixing a product root. There is no
public correlation or restriction to stationary deviations in the proof.

The finite coordinates are bounded, so the closure is compact. Native
AllNever has zero debts and belongs to `C`; therefore the constrained
minimum exists and is at most `r`. The properification estimate

```text
A <= sum_i d_i + 14 M nu^(1/4)
```

has the stated constant. Choose the smallest original Never mass `delta`
and move it to a finite date. The selected player's own cap is unchanged;
its prescribed value changes by at most `2M delta`. Each of the other
three debts changes by at most `4M delta`. The modified profile absorbs
almost surely, and `delta<=nu^(1/4)`. This proves the inequality on actual
profiles. All terms displayed are continuous coordinates on the
augmented carrier, so it passes to `H`.

Consequently a zero constrained minimum would force all debts and
`nu` to be zero, contradicting `A>0`. At a minimizer, `d_h<=r`, so

```text
nu >= ((A-r)/(14M))^4 > 0.
```

This is a bound on retained original Never mass. In particular the later
minimization of `N_h` does attain a strictly positive value.

## Full prefix identity and the constrained comparison

For a fixed root write `Q_i` for forced Quit value, `P_i` for the passive
contribution when at least one opponent quits, `H_i` for opponent
Continue mass, and `s` for joint Continue mass. Let
`C_i=P_i+H_i B_i`, `g_i=Q_i-C_i`. Direct subtraction gives

```text
max(Q_i,C_i) - [q_i Q_i+(1-q_i)(P_i+H_i U_i)]
  = max((1-q_i)g_i,-q_i g_i)+s(B_i-U_i).
```

This is exact on both branches of the maximum. The continuation cap
`P_i+H_i B_i` includes the entire old response menu; the competing
`Q_i` is the new initial query. There is no assumption that the old
supremum is attained. The additional coordinates obey
`N_i'=(1-q_i)N_i` and `e_i'=P_i+H_i e_i`.

These formulas are continuous in the augmented finite coordinates.
Applying the same root to actual realizers proves carrier invariance
without executing a carrier point as an actual tail.

If the three observer coordinates are Nash against `B`, their root
regrets vanish, and prefixing preserves each equation `d_i=0`.
The constrained minimum comparison is therefore legitimate and gives

```text
R_h(q;B) >= m(1-s(q)).
```

It is not an invocation of an unconstrained weighted-minimum theorem
with three zero weights.

## Auxiliary-root bound and the zero-cap blocker

At an exact Nash root against `B-a e_h`, the observer conditions are
unchanged. I checked all three possible `h` cases separately:

- `q_h=0`: the original gap is at most `-H_h a`, and the original
  regret is zero;
- `0<q_h<1`: the original gap is `-H_h a`, and its regret is
  `q_h H_h a`;
- `q_h=1`: the original gap is at least `-H_h a`, and its regret
  is at most `H_h a`.

Thus `R_h<=q_h H_h a`. Writing `H=H_h` yields

```text
m(1-H) <= (a-m)q_h H.
```

For `a<m` this forces the entire root to be AllContinue. Such a root
exists by finite Nash existence, so its singleton best-response
inequalities imply `B_i>=0` for observers and `B_h>=a`. Passage
`a` upward to `m` establishes the nonstrict margin.

Now assume `B_h=m`, choose `a=m+eta`, and take an exact auxiliary
root. The proof correctly retains `q_h>0`: if it were zero, the budget
would force the entire root to be AllContinue, where player `h`
strictly prefers its zero singleton payoff to continuation `-eta`.
For every observer `j`,

```text
q_j <= 1-H <= (eta/m) q_h.
```

In particular `q_j<1` when `eta<m`, so each observer's Nash
condition is `g_j<=0`, including observers who mix.

For a proposed blocker `i` with `B_i=0` and
`Delta_ih=Z_i({i,h})-Z_i({h})=D>0`, the event that the two
other observers continue contributes exactly `q_h D` conditionally.
On its complement every coalition payoff difference is bounded in
absolute value by `2M`; no continuation term remains because `B_i=0`.
The resulting bound is

```text
g_i >= q_h [D(1-2eta/m)-4M eta/m].
```

Choosing `eta/m<D/(2D+4M)` makes this positive. No lower bound on
`q_h`, no choice of a limiting root, and no division before establishing
`q_h>0` is hidden here. This proves that a zero-cap observer cannot
have a positive joining contact against `h`.

## The critical face and the every-minimum quantifier

If the compact set

```text
K={Y in C: J_r(Y)=m and B_h(Y)=m}
```

were nonempty, it would have a point minimizing original `N_h`.
At that point every observer with a positive joining contact has a
strictly positive cap. Finiteness of the player set gives one `p>0`
small enough that

```text
p Delta_ih <= (1-p)B_i   for every observer i.
```

Prefix by a solo `h` root with probability `p`. These inequalities
are exactly the observer-Nash conditions. The pivot cap stays `m`,
its root regret is `p m`, and hence

```text
J_r(Y')=p m+(1-p)m=m,
B_h(Y')=m,
N_h(Y')=(1-p)N_h(Y)<N_h(Y).
```

Thus the prefix lies in the same `K` while violating the defining
least-`N_h` selection. The contradiction removes all of `K`;
it does not merely exhibit one minimizer away from the critical face.
This validates the statement about every minimizer.

At `a=m`, the auxiliary budget forces `H_h=1`. Every observer
therefore Continues, while the pivot gap is `-(B_h-m)<0`.
The pivot also Continues. This proves exact uniqueness at the stated
critical reduced continuation, not only a nonstrict all-Continue
best-response condition.

## Attempts to break the argument and exact scope

The following possible failures were checked and do not occur.

- A compactified tail is not assumed executable: fixed-root continuity
  is used instead.
- A finite cap maximizer is not assumed: the full supremum is carried
  through the exact maximum formula.
- The auxiliary roots need not vary continuously with `eta`.
- Zero observer caps do not obstruct choosing the solo probability:
  the preceding auxiliary-root argument gives precisely their needed
  nonpositive contact sign.
- Repeated solo prefixes are not asserted to keep a fixed positive
  rate indefinitely. The proof needs only one feasible prefix at a
  least-original-Never point.
- No native positive-`A` example is inferred from the algebraic tests.
  Such an example would itself require solving the original negative
  problem.

The hypothesis `A>0` has indispensable jobs: it gives `m>0` and
retained `N_h>0` on the relevant minimum set. Without it, the zero
table has an absorbing zero-debt minimizer with `m=B_h=0`, so the
strict conclusion fails. It would also be incorrect to replace
original `N_h` by Never mass in a weak limit of clocks.

The result is not essentially four-player. For a finite number `n`
of players the same proof works with properification constant
`(4n-2)M`, exponent `1/n`, and the corresponding bound over `n-2`
other observers in the blocker estimate. This observation does not
produce an additional Fin4 class or justify a separate export.

## Source, overlap, and coverage assessment

I inspected these exact declarations statically, without running Lean:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
- `minimumTerminalSemantic_weightedAuxiliaryNash_budget`,
  `minimumTerminalSemantic_weightedAuxiliaryNash_criticalFace`, and
  `minimumTerminalSemantic_weightedSingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean`;
- `minimumTerminalSemantic_auxiliaryNash_criticalFace` and
  `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `QuittingSingletonTightMinimumFace`,
  `singletonTight_owner_debt_eq_capDefect_add_liveTail`, and
  `isZeroQuittingRootNash_solo_of_singletonTightMinimumFace` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean`;
- `positive_minimum_preemptedOwner_quadraticMargins` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.

The full-carrier weighted minimum and singleton-tight theorems use
different minima and do not immediately give this constrained
`d_h+r nu` statement. The earlier reviewed
[strict-solo constrained plateau note](../notes/CODEX_MINER__FIN4_STRICT_SOLO_REGENERATION_PLATEAU_BOUNDARY.md)
already supplies constrained root isolation and an all-Continue plateau
under a full terminal-gap source and punishment floors. It does not
contain the present native positive-absorbing-gap critical-face exclusion
with original Never penalty. Conversely the present note does not
resolve that earlier plateau or transport its punishment-floor
information.

The actual incoming positive-`A` source supplies all hypotheses of this
theorem; no unproduced strategy witness is assumed after that source.
The strict inequality therefore removes a real previously unexcluded
mode of this constrained source description. It should be recorded as
that precise refinement. It is not an equilibrium producer, an
absorbing return, or a reward-table characterization. There remains an
entire interior constrained minimum with `B_h>m`.

My coverage recommendation is **retain internally pending a substantive
consumer or a larger consolidated reduction**. The new strict face
exclusion alone should not be reported as a significant reduction of
the raw possible-counterexample reward tables. A mathematical PASS
does not itself pass the export significance gate.

More precisely, the source adapter passes: every native positive-`A`
table has these constrained minima for every `h` and `0<r<A`. The
objection is not a missing source premise. The new equality face is a
boundary of this recently introduced auxiliary constrained problem,
and the note identifies no previously established conjecture-facing
consumer or live payoff stratum which this exclusion completes.
Every still-possible positive-`A` table remains represented by an
interior constrained minimum. The strict margin is only at fixed
`r`; no uniform lower bound as `r` decreases to zero is proved.
Consequently it does not eliminate a zero-payoff stratum of the
existing least-Never, zero-debt source by passage to that limit.
These are the reasons for **not passing the standalone export
coverage gate**, rather than a claim that a reduction must always
prove a new raw-table UE class.

The topological discussion in Section 7 is not used by the theorem.
I checked the dependency's proper-clock screening, finite-game
continuation reduction, and Dini/uniform-query explanation at the
level stated. It does not yield a continuous cap along an arbitrary
observer-equilibrium path or cross from the retained positive-Never
source to the proper-clock absorbing face. No such claim is needed.

## Reproduction and next proof obligation

The source checker was read and independently replayed:

```text
python math/experiments/CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_CHECK.py
PASS: 900 full prefix identities; 10 observer-Nash repairs;
200 auxiliary bounds; 243 critical-face lower bounds;
512 exact solo-prefix controls.
```

The core identities and inequalities above were also derived directly,
independently of the checker. Its finite exact tests support algebraic
regression only; they do not prove the global compact argument.

The remaining target is an observer-feasible nonlocal change with total
pivot regret strictly below `m` times its absorption loss. Exact roots
at the critical reduced continuation cannot supply it: the theorem
proves that every one is inert. A successful continuation must use
additional information about the same source's complete cap menu or
change a whole part of its laws, while keeping the original constrained
objective account. Merely relabeling its positive pivot payoff or
choosing another root at the same `w` does not do that.
