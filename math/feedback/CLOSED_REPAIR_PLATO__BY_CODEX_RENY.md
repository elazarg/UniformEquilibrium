# Independent mathematical review of CLOSED_REPAIR_PLATO

Reviewer: CODEX_RENY. Entire original packet read before any other review.

Reviewed source: `gpt/CLOSED_REPAIR_PLATO.md`, 395 lines, SHA-256
`8729d00056bac7bbb6c8ef8293fa450b07a356579c1f7e1b597e0dacdcd097bf`.

**Verdict: PASS.** The complete source, optimal-repair characterization,
all-selector closed-family theorem, and outside equilibrium are correct.
No substantive mathematical repair is required. This is an independent
ordinary-mathematics assessment, not a Lean check or an export decision.

The attached sandbox verifier was unavailable and was not trusted. I wrote
and ran a separate exact-rational coalition evaluator in
[CLOSED_REPAIR_PLATO__BY_CODEX_RENY_CHECK.py](CLOSED_REPAIR_PLATO__BY_CODEX_RENY_CHECK.py).
It independently reproduced every displayed payoff/cap/debt, the three
pivot coefficient rows, all fifteen nonpivot event coefficient rows,
certificates (2), (5)–(7), and their equality cases. Additional multi-atom
law tests checked the event reduction with distinct gaps and late dates.
The proofs for arbitrary infinite laws are given below; finite tests alone
would not establish that scope.

A self-contained mathematical preservation, including the complete reward
table and all fifteen coefficient rows, is
[CODEX_RENY__CLOSED_UNILATERAL_REPAIR_FAMILY.md](../notes/CODEX_RENY__CLOSED_UNILATERAL_REPAIR_FAMILY.md).
It attributes the result to the original external author.

## 1. Exact statement checked

In the complete four-player reward table, Never pays zero and the own
singleton vector is (1,0,0,0). All players' randomization is independent.
Full caps range over arbitrary behavioral responses, equivalently over
arbitrary stopping laws on ℕ∪{Never}. Let E be maximum terminal regret.

The source p has independent half-zero, half-Never clocks. The family F
keeps the three nonpivot clocks fixed and gives the pivot masses 1/2 at
zero, 1/4 on an arbitrary probability law G on positive finite dates, and
1/4 at Never. The theorem establishes:

- p is exact finite-menu Nash on {0,Never}, with full debts (1/8,0,0,0).
- Against p's fixed opponents the optimal unrestricted pivot repair has
  value z=3/32, and **all** minimizers are exactly F.
- Every member of F has debts (3/32,3/32,3/32,1/32).
- Every unilateral change with E≤z stays in F. Nonpivots must retain
  their literal stopping laws; the pivot may only retime G.
- The same reward table has a pure exact date-zero equilibrium, so its
  joint global full-regret infimum is zero.

I checked the distinction between finite-menu Nash and full Nash: the
source deliberately has positive late pivot debt and is not full Nash.

## 2. Source and all optimal pivot repairs

Independent evaluation gives

```text
U(p)=(0,1,−7/8,−1/8),
B(p)=(1/8,1,−7/8,−1/8).
```

Every player's date-zero and Never values equal its prescribed value.
For the pivot, any positive date additionally earns one on the all-
opponent-Never event, of probability 1/8. Other players have zero own
singletons, so their positive finite values equal Never. This proves the
exact displayed-menu source and its unrestricted debt.

For an arbitrary pivot law, let u,λ,ν be its zero, positive finite, and
Never masses. The exact coefficient vectors of (D₀,N₁,N₂), respectively
on these three mass categories, are

```text
u: (1/8,−13/8,1),
λ: (0,2,−5/8),
ν: (1/8,13/8,−1).
```

Their convex combination with weights 3/4, 2/21, 13/84 equals 3/32 on
every category. All weights are strictly positive and sum to one. Each
quantity is bounded above by full E, even if a displayed Never gain is
negative. Therefore E≥z for every pivot law.

At equality each positively weighted term must equal z. D₀=z gives
λ=1/4; using u+ν=3/4 and N₂=z gives u=1/2, ν=1/4. Thus the argument
characterizes all minimizing laws, not only one geometric or finite law.

The converse is also valid for every G. After surviving date zero, the
nonpivot's reward for waiting for the pivot singleton is a_j=(3,3,1)_j,
whereas collision rewards are b_j=(0,3,−2)_j and own singleton rewards
are zero. Since a_j≥max(b_j,0), Never dominates every positive finite
response pathwise. This includes the equality a₂=b₂=3 and zero-probability
dates. The full cap is therefore the maximum of date zero and Never.
The resulting U and B are exactly the packet's values, independent of G.

## 3. Why the five-event reduction is genuinely infinite-law complete

Fix a nonpivot mover j and independently draw S∼G and T∼μ. Because S
is positive finite almost surely, the events T=0, T=Never, S<T<Never,
S=T<Never, and T<S exhaust the probability space. They have masses
x,n,a,b,c with sum one.

The two unchanged nonpivot clocks are each zero or Never. Conditional on
each of their four outcomes and on the pivot's original zero/G/Never
branch, the terminal coalition depends only on which of the five events
occurs. No distance between S and T matters. The same is true of:

1. Every prescribed payoff used in the certificate.
2. The pivot's complete G response, because a fresh G response has the
   same independent joint distribution with T. Reusing S in a coupling
   of expectation calculations does not introduce public correlation.
3. Every Never response used in the certificate.
4. The limiting late-pivot response. Bounded convergence gives its value
   on each opponent-clock sample: the finite first-opponent reward if
   one exists, and the pivot singleton one otherwise.

The late limit L is at most the full cap minus U because it is a limit of
legal response gains. Its supremum need not be attained by Never or by
one finite date. The proof does not conflate those actions.

Although D_j is called a full debt, it introduces no hidden nonlinearity
in this calculation. The mover's opponents remain fixed at the original
family member. Its cap is the same constant computed in Section 2, and
Never attains that cap. Thus D_j is itself its Never gain and is affine
in x,n,a,b,c.

I recomputed all five coefficient rows for each mover directly from the
reward table. These yield exactly

```text
(29/38)D₁+(51/380)H+(9/380)L+(3/38)N₂
    =3/32+(9/76)b;
(91/106)D₂+(3/53)L+(9/106)N₁
    =3/32+(15/848)a+(9/53)c;
(7/10)L+(11/40)N₁+(1/40)N₂
    =3/32+(29/160)a+(21/128)b.
```

All three weight vectors are strictly positive probability vectors. The
identities hold throughout the formal five-weight simplex, so they hold
in particular on the potentially smaller set achievable by independent
S and T for a fixed G. No unjustified freedom of the five event masses
is needed.

## 4. Falsification attempts at equality and neutral retiming

The closure theorem needs the equality cases; mere E≥z would only give
a single-state coordinate trap. I checked these cases separately.

- Player 1: equality forces b=0 and D₁=H=L=N₂=z. The unrestricted
  coefficient formulas are D₁=3(x+b+c)/16 and H−L=5(a+b)/4.
  Under b=0 these are exactly the packet's formulas. They imply a=0,
  x+c=1/2, n=1/2; then N₂=z+c/2 forces c=0.
- Player 2: equality forces a=c=0. The exact D₂=3(x+c)/16 yields
  x=1/2, after which L=z+3b/16 forces b=0 and n=1/2.
- Player 3: equality forces a=b=0. The exact L=N₁=z equations are
  5x+3c=5/2 and 15x+7c=15/2, forcing c=0, x=n=1/2.

Thus in all three cases the **entire** positive finite mass a+b+c
vanishes. The nonpivot law is literally unchanged, including at dates
outside G's support. This is stronger than an equality of terminal laws
or of realized payoff vectors. Pivot replacements are exhausted by the
earlier three-mass calculation and preserve exactly F.

I explicitly tested multi-atom G and mover laws having dates before,
between, equal to, and after G's atoms. The same formulas passed exact
rational evaluation. Their infinite-support justification is the event
partition argument, not extrapolation from these tests.

## 5. Limit and information-mode boundaries

The natural interpretation of the weak-limit paragraph is weak convergence
on the one-point compactification ℕ∪{Never}. At any such limit, the
isolated date-zero mass remains 1/2, and Fatou gives positive finite
pivot mass λ≤1/4. Opponents are unchanged. The pivot cap remains 1/8
and its payoff is λ/8, hence its actual debt is (1−λ)/8≥z. This
conclusion uses a direct cap calculation, not weak continuity of payoff
at Never. If no weak law limit is taken, every finite iteration is already
in F at regret z.

All conclusions about an unchanged strategy are properly conclusions about
its induced stopping law. They do not prohibit irrelevant modifications
on histories of zero reach. The packet's own more precise wording uses
“law,” so no mathematical amendment is needed.

No opponent detects the pivot's private mixture or conditions on a hidden
branch. The certificate responses G, Never, and deterministic late Quit
are ordinary ex ante unilateral alternatives.

## 6. Outside equilibrium and the exact algorithmic implication

At the pure profile with player 0 quitting at zero and all others Never,
the payoff is (1,3,3,1). The nonpivot joining rewards (0,3,−2) do not
improve it. The pivot gets its maximal value one against all-Never
opponents. All later responses either preserve the already absorbed
outcome or give the pivot the same singleton one. This verifies exact
terminal Nash and, directly at date zero, the claimed uniform payoff.

This pure equilibrium already belongs to the same one-date finite menu.
Consequently the joint global geometric-repair minimum is zero there.
The positive source and F are **not** global optimizers, even at that
same finite calendar. The active joint-global-minimum contraction route
is therefore untouched.

The eliminated guarantee is precise: start from every actual finite-menu
exact Nash source, optimally repair its pivot against the unchanged
opponents, then choose E-nonincreasing complete unilateral replacements
so that full regret tends to zero. On this table and this source, every
optimal first repair and every subsequent allowed choice stays trapped.

The theorem does not rule out a better initial source, a nonoptimal first
move, coordinated changes of several laws, or controlled temporary
increases. In particular it does not show that every monotone protocol
starting directly from p is blocked unless its first operation is the
specified optimal pivot repair.

## 7. Narrow source overlap and export relevance

The exact finite-menu semantics were checked in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`, notably
`quittingFiniteDeadlineTimingGame`,
`quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`, and
`quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU`.
`quittingFiniteDeadlineReplyCap_eq_sup_pureTimeTerminalValue` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean` identifies
only the displayed-menu cap, not the extra unrestricted late pivot value.
The latter is computed explicitly here. The geometric-compression export
already gives exact pivot optimization and explicitly disclaims a general
monotone repair algorithm; this packet does not replace that LP theorem.

I read the complete prior H comparison in
`notes/CODEX_FRECHET_CYCLE__PIVOT_LP_CANONICAL_JOINT_CALENDAR_TRAP.md`.
It proves a full-law coordinatewise global minimum at one specified
profile, a genuinely joint escape, and an allowed cycling sequence. It
does not prove closure under **every** neutral unilateral change of the
entire minimizing family. The earlier generic negative-singleton trap in
`CODEX_SKEPTIC__GLOBAL_PORTFOLIO_REFINEMENT_AUDIT.md` likewise does not
provide this source-derived all-selector closure theorem.

The extra quantifiers in the new packet are therefore substantive in this
bounded comparison: exact finite-menu provenance, all optimal first
repairs, every later nonincreasing unilateral choice, arbitrary retiming,
and arbitrary infinite laws. That is useful evidence against arbitrary-
source coordinate-repair algorithms, beyond a single bad tie-breaking
example. It is not a new obstruction to joint global minimization, a
producer from arbitrary tables, or a conjecture counterexample.

Whether this stronger algorithmic boundary warrants a separate export is
an editorial/gate decision, not a consequence of this PASS. No source or
export was edited, and no new L/A/C status is asserted.
