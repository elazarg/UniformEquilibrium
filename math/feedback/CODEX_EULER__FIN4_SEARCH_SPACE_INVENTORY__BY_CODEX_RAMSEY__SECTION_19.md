# Independent review of Section 19 in `CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY`

Reviewer: `CODEX_RAMSEY`

## Verdict

**REVISE → PASS after one wording repair.**  The construction, endpoint
signs, quantitative hazard and atom constants, unrestricted behavioral-cap
equalities, debtor localization, and paid-row decoder are all correct.

In Corollary 19.2 replace

> has exactly one of the following semantic outcomes

by

> has at least one of the following semantic outcomes.

Theorem 18.1 is an inclusive alternative: a pair may have both a member-leave
and an outsider-join witness.  No exclusivity is proved or needed.  After
this literal repair, I find no mathematical objection.

## Induced Nash sign and quantitative free absorption

With base `{k,i}` sure, force player `j`'s action and let `o` Quit with
probability `y`.  The displayed pair-to-triple inequality is precisely

```text
Delta_j(0)=r({k,i,j})_j-r({k,i})_j>=Gamma.
```

At `y=1`, the two forced-action rewards differ by at least `-2M`.  Affineness
therefore gives

```text
Delta_j(y)>=(1-y)Gamma-2My.
```

If `x=q_j(Quit)=1`, free-player absorption is one.  If `x<1`, Continue has
positive support in the selected induced Nash law, so the exact support
condition has the correct direction `Delta_j(y)<=0`.  Hence

```text
y>=Gamma/(Gamma+2M)=alpha.
```

The reward bound and the strict terminal gap imply `Gamma<=2M`; in
particular the denominator is positive and `0<alpha<=1`.  Since

```text
1-(1-x)(1-y)>=y,
```

item `(19.5)` follows.

## Atom calculation

The pairwise-distinct literal `Fin 4` labels make `{k,i}` and `{j,o}` a
partition of the player set.  Independence gives exactly

```text
(1-x)y,  x(1-y),  xy
```

for the three strict supersets of the sure base (up to the harmless order in
which the first two are displayed).  Their sum is

```text
x+y-xy=1-(1-x)(1-y)>=alpha,
```

so one atom has mass at least
`alpha/3=Gamma/[3(Gamma+2M)]`.  There is no omitted terminal outcome because
the base absorbs surely at date zero.

## Unrestricted caps, debt support, and decoder

After an arbitrary behavioral deviation by either free player, both base
players still Quit at date zero.  Thus only the deviator's date-zero Boolean
marginal matters.  Membership in
`quittingPersistentBaseNashSet reward base free` says its selected marginal
attains the larger forced endpoint, so the prescribed payoff equals the
full behavioral cap—not merely a stationary cap—in both free coordinates.
The punishment upper leg then gives both floor inequalities.

Terminal exploitability of the actual stationary profile supplies some
coordinate with behavioral debt at least `Gamma`.  The two free debts are
zero, so the debtor lies in the sure base `{k,i}`.  Rewriting the stationary
semantic envelope as the stationary unilateral cap, the checked
Quit-now/Never endpoint decoder and then the paid first-disagreement decoder
produce `(19.10)` with the same profile, opponents, witness gap, and debtor.

## Constructor and scope

Nonemptiness of the complete induced Nash set is the named checked theorem;
no selection continuity is assumed.  The full pairing of literal `Fin 4`
labels supplies disjoint base/free sets and no outside coordinate.

The result creates an actual stationary carrier source with at most two
debtors, two all-behavior solved coordinates, a fixed nonsingleton atom, and
a paid row.  It does not make either sure-base owner a best response, prove
the prescribed vector is floor safe in the base coordinates, identify the
heavy atom with exact Bellman charge, or produce a return.  Corollary 19.2
therefore consumes the static triple-join chamber into the common paid-source
lane, but it is not itself a paid-near-return consumer or a well-founded
descent.  That noncompiler scope is stated correctly.

