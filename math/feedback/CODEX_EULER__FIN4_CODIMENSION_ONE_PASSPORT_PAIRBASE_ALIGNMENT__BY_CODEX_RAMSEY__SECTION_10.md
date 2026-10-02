# Independent falsification of Section 10: codimension-one solo carrier descent

Reviewer: `CODEX_RAMSEY`

Note reviewed:
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](../notes/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md),
Section 10 only.

Verdict: **REVISE -> PASS after one substantive proof repair and bounded
notation/source repairs.**  The carrier selector, opponent-absorption constant
`gamma/(12M)`, unique-debtor contraction, fixed drop
`gamma^2/(12M)`, and separation above the minimum fiber are mathematically
valid.  The written inference `d_e(R)>=gamma` from the immediate singleton
gap is not valid: immediate Quit in the next suffix can collide with the
retained players.  The conclusion is nevertheless recovered exactly from the
terminal exploitability witness after the three retained debts vanish.  This
replacement is mandatory.

## Claim checked

Under the strict nonsingleton insertion-cap residual

```text
C_e(I\{e}) <= gamma-eta,  eta>0,
```

the note selects a semantic carrier pair `R` with only possible debtor `e`, a
literal solo comparison `r_e({e})-R.1_e>=gamma`, and an exact prescribed-tail
root `q` whose opponents of `e` absorb with probability at least
`alpha=gamma/(12M)`.  For `R'=Prefix(q,R)` this is claimed to imply

```text
D(R') <= (1-alpha)D(R),
D(R)-D(R') >= gamma^2/(12M),
D(R) >= D_*+gamma^2/(12M).
```

The result is semantic and explicitly does not claim punishment-floor
admissibility, preservation of the solo gap, graftability, iteration, or a
uniform payoff.

## 1. Conditional-suffix selection

This part passes.

For each retained three-player terminal error `epsilon_n->0`, the reviewed
operational deletion theorem gives the same deleted label `e` and some finite
pure quit time with full gain `gamma`.  The decomposition

```text
Delta_n = c_n x_n+(1-c_n)y_n,
w_n Delta_n>=gamma
```

has `x_n<=2M` and `y_n<=C_e(J)<=gamma-eta`.  Hence

```text
x_n>=gamma,
w_n>=gamma/(2M),
c_n>=eta/(2M-gamma+eta).
```

The denominator is positive because the same bounded payoff comparison gives
`0<gamma<=2M`.  Thus the next-suffix event has the uniform lower bound

```text
rho = gamma*eta/[2M(2M-gamma+eta)]>0.
```

A retained-player deviation in the conditional suffix can be inserted after
that publicly observed survival history, so terminal `epsilon_n`-Nash gives

```text
d_j(R_n)<=epsilon_n/rho  (j!=e).
```

The terminal semantic carrier is compact, prescribed payoffs and debts are
continuous, and the next-suffix prescribed coordinate is the literal Never
value used in `x_n`.  Passing to a subsequence therefore proves

```text
d_j(R)=0 (j!=e),
r_e({e})-R.1_e>=gamma.
```

The proof should cite
`exists_terminalNash_deleteBlock_of_card_le_three` (or the underlying
card-three uniform-payoff theorem) for the sequence of retained terminal
profiles.  “Retain the hypotheses of Theorem 3.1” by itself only fixes one
epsilon-profile.  In Fin4 the required all-errors producer is checked, so
this is a source citation/statement repair rather than a mathematical gap.

## 2. Mandatory repair of the owner-debt lower bound

The written sentence

> immediate Quit is a legal behavioral deviation, so `d_e(R)>=gamma`

does not follow from `r_e({e})-R.1_e>=gamma`.  The pair `R_n` begins at time
`t_n+1`.  If `e` Quits immediately in that suffix, retained players may also
Quit at its first row, so the forced-Quit payoff is an average of collision
rows, not necessarily `r_e({e})`.  The solo comparison was created at the
*previous* selected row after conditioning on retained Continue there; it is
valid for the artificial all-opponents-Continue endpoint used later, but is
not by itself an unrestricted-debt lower bound at `R_n`.

There is an exact repair using the maintained witness.  Each `R_n` is the
semantic pair of an actual conditional-suffix behavior profile.  Apply the
checked theorem

```text
QuittingTerminalExploitabilityWitness.
  exists_terminalGap_le_terminalSemanticDebt
```

from `TerminalSemanticPlateauTightness.lean`.  It gives some coordinate of
`R_n` with debt at least `gamma`.  For all sufficiently large `n`, every
retained coordinate has debt at most `epsilon_n/rho<gamma`, hence the selected
coordinate must be `e`.  Therefore

```text
d_e(R_n)>=gamma eventually,
d_e(R)>=gamma
```

by continuity.  This supplies exactly the lower bound needed below without
misreading simultaneous Quit as a singleton guarantee.

## 3. Opponent-absorption constant

This part passes, including the constants.

Choose any exact product Nash root `q` against `R.1` and put
`A=A_{-e}(q)`.  If `A<gamma/(12M)`, then every opponent Quit marginal is at
most `A`.  Against the all-Continue comparison row, the sum of the three
opponent Bernoulli TV distances is at most `3A`.  The checked estimate

```text
abs_quittingRootEndpointDifference_sub_le_opponentTVSum
```

therefore moves player `e`'s endpoint difference by less than
`4M*3A<gamma`.  The literal singleton gap at `R.1` makes the comparison
difference at least `gamma`, so `e` strictly prefers Quit at `q`; exact
complementarity forces `q_e=1`.

Let `c!=e` be the checked full-gap singleton collider.  Compare `q` with the
row having `e` sure Quit and the two labels outside `{e,c}` Continue.  The
`e` marginal now agrees exactly, and only two remaining TV terms occur, so
the endpoint difference moves by less than

```text
4M*2A < 2gamma/3.
```

The reference collision difference is at least `gamma`; hence `c` strictly
prefers Quit and exact complementarity forces `q_c=1`.  This contradicts
`A<alpha<1`.  Thus every exact root has `A>=alpha`.  The argument uses the
same witness gap and same-table collider from
`exists_terminalGap_collision_at_singleton`; label and orientation are
correct.

The tail bound required by the TV theorem should be stated: since `R` is in
the carrier and all terminal rewards (including zero nonabsorption payoff)
lie in `[-M,M]`, every coordinate of `R.1` also lies in that interval.

## 4. Debt contraction and minimum separation

This part passes after the owner-debt repair.

Exact prefixing weakly decreases every nonnegative debt coordinate.  The
three zero coordinates therefore remain zero.  For the unique possible debtor
`e`, either unfold the exact block action in
`quittingTerminalSemanticDebt_prefix_eq_blockAct` or invoke
`quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul`
from `TerminalSemanticFinFourSoloWallDispatch.lean`; it gives

```text
D(R')<=O_e(q)D(R)=(1-A)D(R)<=(1-alpha)D(R).
```

The repaired `D(R)=d_e(R)>=gamma` yields the fixed drop
`alpha*gamma=gamma^2/(12M)`.  Since `R'` remains in the semantic carrier,
`D_*<=D(R')`, and adding the drop gives the claimed separation of `R` from
the global minimum fiber.

## 5. Bounded exposition repairs

Before treating the section as final, also repair:

1. define `C_e(J)` locally as the checked block-join cap
   `max({0} union {T(S): nonempty S subset J})`;
2. distinguish that passport symbol from the punishment value used in the
   final floor caveat;
3. fix the literal `quad`, `qquad`, and extra parenthesis in `A_{-e}(q))`; and
4. name the card-three terminal all-errors source and the unique-debtor
   contraction theorem explicitly.

These are statement/proof-writing repairs only.

## 6. Exact scope

With the mandatory debt-localization repair, Section 10 is a genuine
conjecture-facing producer: it turns the remaining strict solo chamber into
an actual carrier source and one exact, quantitatively charged semantic debt
descent.  It still does not provide a punishment-floor tail, preserve the
solo comparison after prefixing, graft the conditional source beneath the
old quiet lift, or define a regenerating finite rank.  No export is recommended
until at least one of those two stated seams is consumed.
