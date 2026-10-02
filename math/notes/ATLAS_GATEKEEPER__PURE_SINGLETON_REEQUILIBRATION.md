# Pure-singleton re-equilibration: the one-active wall is real

## Status

The proposed pure-singleton reduction is correct when the owner's Continue
option is evaluated at the literal tail **cap** `B_j(Z)`.  Re-equilibrating the
other three players at date zero makes all three outsider behavioral debts
zero because the owner still Quits surely under every outsider deviation.
Positive global minimum then forces a strictly positive owner
Continue-versus-Quit defect.

The strongest automatic consumer is an exact two-arm statement:

* equality with `D_*` gives an actual minimum-fiber point whose positive debt
  support is the singleton owner; or
* strict inequality gives a compact, quantitatively positive off-minimum
  one-active wall.

Varying the owner's hazard while re-equilibrating outsiders does not consume
the strict arm.  An exact four-player regression below has a unique outsider
equilibrium for every hazard, an affine/continuous semantic path, and total
debt strictly increasing away from the all-Continue endpoint.  The regression
also shows concretely why replacing `B_j(Z)` by `U_j(Z)` gives the wrong
answer.

This is ordinary mathematics, not a checked Lean addition.

## Declarations inspected

`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`

* `quittingPersistentBaseNashSet`
* `quittingPersistentBaseRoot`
* `quittingPersistentBaseNashSet_nonempty`
* `quittingPersistentBaseRoot_free_purePayoff_le`

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean`

* `persistentBase_inducedNash_free_semantics`

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`

* `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`
* `minimumTerminalSemantic_absorption_mul_debtSum_le_capDefect`

`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`

* `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`

`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean`

* `FinFourSingletonBaseSameLawResetProducer`

The last structure is related but not a duplicate of the source-matched
statement below.  It uses a stationary singleton-base source.  With an
arbitrary literal tail `Z`, the owner's deviation to Continue can expose
`Z`, so its cap genuinely depends on `B_j(Z)`.

## 1. Exact sure-owner reduction

Fix a literal behavioral tail `Z` and an owner `j`.  Let the date-zero root
`x` prescribe `j` to Quit surely.  On the other three players choose a mixed
Nash equilibrium of the finite game in which their payoffs are the rewards of
the date-zero coalition containing `j`.

Such a Nash equilibrium exists.  For an outsider `i`, every unilateral
behavioral deviation still faces the sure Quit of `j`, so absorption occurs at
date zero.  All later behavior is irrelevant, and the finite-game Nash
condition is exactly the unrestricted behavioral best-response condition.
Consequently

$$
d_i(x\triangleright Z)=0\qquad(i\ne j).
\tag{1}
$$

For `j`, define

$$
Q_j(x)=\mathbb E[r_j(\{j\}\cup A)]
\tag{2}
$$

when `j` Quits, where `A` is the outsiders' date-zero quitting coalition, and

$$
C_j(x;Z)
=\sum_{A\ne\varnothing}\Pr(A)r_j(A)
 +\Pr(A=\varnothing)B_j(Z).
\tag{3}
$$

Equation (3), not the expression with `U_j(Z)`, is the Continue value in the
owner's unrestricted cap.  If the owner Continues and all outsiders Continue,
the owner may use an arbitrary behavioral best response in the literal tail.
Thus

$$
d_j(x\triangleright Z)=\bigl[C_j(x;Z)-Q_j(x)\bigr]_+.
\tag{4}
$$

The joint Continue mass of `x` is zero.  Hence (1)--(4) also follow directly
from the checked arbitrary-root identity

$$
d_i(T_xz)=\operatorname{Def}_i(x;B(z))
 +c(x)d_i(z).
\tag{5}
$$

If the same reward table has positive global minimum `D_*>0`, the actual
profile `x ▷ Z` has total debt at least `D_*`.  Combining this with (1) gives

$$
\boxed{
C_j(x;Z)-Q_j(x)
=d_j(x\triangleright Z)
=D(x\triangleright Z)
\ge D_*>0.}
\tag{6}
$$

The positive part disappears in (6) because the lower bound is strict.  No
attainment of `B_j(Z)` by one deviation is required; pure-time or behavioral
near-cap witnesses give gains arbitrarily close to the displayed defect.

## 2. The compact one-active wall

The outsiders' finite Nash set is nonempty and compact, and the function

$$
x_{-j}\longmapsto C_j(x;Z)-Q_j(x)
$$

is continuous.  Therefore it has an attained minimum `G_j(Z)` over that Nash
set.  Equation (6) yields

$$
\boxed{G_j(Z)\ge D_*.}
\tag{7}
$$

This gives the exact exhaustive conclusion available at the sure-owner
endpoint.

### Equality arm

If `G_j(Z)=D_*`, a minimizing outsider Nash produces an actual global
minimum with

$$
\operatorname{supp}_+ d=\{j\}.
\tag{8}
$$

This is a genuine finite support-rank drop whenever the retained source
minimum has at least two positive-debt coordinates.  If the retained source
is already one-active, (8) enters the maintained one-active minimum branch
rather than decreasing rank.

### Strict arm

If `G_j(Z)>D_*`, compactness supplies a positive margin

$$
\eta=G_j(Z)-D_*>0
\tag{9}
$$

and every re-equilibrated pure-singleton endpoint lies at least `eta` above
the minimum fiber.  This is a source-matched owner wall, but it is not a
charged return: no exact path entering and leaving that wall has been
constructed.

## 3. Hazard interpolation and the payment identity

Now prescribe owner hazard `p in [0,1]` and choose an outsider Nash in the
finite root game evaluated against the cap vector `B(Z)`.  Let `x_p` be the
resulting root, let

$$
c_p=\Pr_{x_p}(\text{all Continue}),
$$

and let `delta_j(p)` be the owner's root coordinate Nash defect against
`B(Z)`.  Every outsider root defect is zero.  The exact cap--debt recursion is

$$
\boxed{
D(x_p\triangleright Z)=c_pD(Z)+\delta_j(p).}
\tag{10}
$$

If `Z` itself realizes a global minimum, (10) and global minimality give the
absorption-payment inequality

$$
\boxed{
\delta_j(p)\ge (1-c_p)D_*.}
\tag{11}
$$

Thus every unit of absorption created by this partial Nashification must be
paid by the one unsolved owner coordinate.  Repeating small hazards does not
make this payment disappear: before such roots could be stacked, their
continuation caps would also have to be matched, and (11) is the exact local
cost at every minimum tail.

At `p=0`, the all-Continue outsider equilibrium recovers the delayed tail.
At `p=1`, (7) is recovered.  Neither continuity of payoffs nor continuity of
an equilibrium selection forces another point on the minimum fiber.

## 4. Exact Fin4 regression: unique continuous re-equilibration moves away

Let players be `0,1,2,3`, with owner `0`, and choose a rational
`0<epsilon<1`.  For every nonempty coalition `S`, define

$$
r_0(S)=
\begin{cases}
2,&1\in S,\ 0\notin S,\\
1,&0,1\in S,\\
0,&1\notin S,
\end{cases}
\tag{12}
$$

and, for `i=1,2,3`,

$$
r_i(S)=
\begin{cases}
\epsilon,&i\notin S,\\
0,&i\in S.
\end{cases}
\tag{13}
$$

Let the literal tail `Z` prescribe players `0` and `1` to Quit surely at its
first date and players `2,3` to Continue.  Then

$$
U_0(Z)=1,\quad B_0(Z)=2,\quad d_0(Z)=1,
$$

$$
U_1(Z)=0,\quad B_1(Z)=\epsilon,\quad d_1(Z)=\epsilon,
$$

and `d_2(Z)=d_3(Z)=0`.  Hence

$$
D(Z)=1+\epsilon.
\tag{14}
$$

For `p in [0,1]`, prefix `Z` by the root at which player `0` Quits with
probability `p` and all three outsiders Continue surely.  For every `p`, each
outsider obtains `epsilon` by Continue in the cap game and `0` by Quit.  Thus
all-Continue is the **unique** outsider Nash; there is no equilibrium-selection
discontinuity to exploit.

The complete semantic debts are

$$
d_0(p)=1+p,
\qquad
d_1(p)=(1-p)\epsilon,
\qquad
d_2(p)=d_3(p)=0,
\tag{15}
$$

and therefore

$$
\boxed{
D(p)=1+\epsilon+p(1-\epsilon).}
\tag{16}
$$

The path is affine and strictly increasing.  At `p=0` it is the delayed tail;
at `p=1` it is a pure-singleton source with all outsider debts zero and owner
debt `2`.  The one-active defect persists and becomes larger.

At the root, the owner's Quit value is `0`, while its Continue cap is
`B_0(Z)=2`.  Using the prescribed tail value `U_0(Z)=1` would understate the
root defect by a factor of two at `p=1` and would break the exact recursion.

This table has an all-Never zero-debt profile, so it is not a counterexample
and does not instantiate `D_*>0`.  Its purpose is sharper: it satisfies the
literal tail, unique outsider re-equilibration, strict owner
payoff-above-singleton separation at the tail, and boundary continuity, yet
the hazard path has no return to its starting debt level for `p>0`.  Global
minimality would permit exactly this strict outward motion; it does not reverse
its sign.  All rewards in (12)--(13) are nonnegative and every own singleton
reward is zero; all-Never therefore also shows that every punishment value is
zero.  Thus the regression satisfies punishment normality as well.

## Verdict

The pure-singleton re-equilibration claim is valid and useful, but it is not a
terminal-approximation producer.  Its strongest source-matched output is

$$
\boxed{
\text{minimum-fiber singleton-support endpoint}
\quad\lor\quad
\text{uniform positive one-active off-minimum wall}.}
$$

The first arm is a genuine rank consumer.  The second is not consumed by
varying the owner hazard; the regression (12)--(16) rules out a continuity or
intermediate-value proof from the supplied local data.  Consuming the strict
wall requires a new operation that returns from it with exact
punishment-floor/cap provenance, or converts its fixed owner premium into a
minimum-fiber support transition.

## Atlas self-audit: the strict wall is not a checked solo gate

The phrase "one-active wall" above refers to **positive semantic-debt
support**:

$$
\operatorname{supp}_+d(x\triangleright Z)=\{j\}.
\tag{17}
$$

It must not be identified with a one-active exact root, a solo semantic spine,
or a `FinFourChargedSoloBlockerGate`. Inspection of the exact theorem
interfaces shows that neither
`TerminalSemanticFinFourSoloWallDispatch.lean` nor
`TerminalSemanticFinFourOffMinimumChargedBlockerGate.lean` automatically
consumes the strict arm.

### Why `TerminalSemanticFinFourSoloWallDispatch` does not apply

At the sure-owner source constructed above, the current root is not exact:
the unique positive debt is precisely the owner's positive root defect

$$
C_j(x;Z)-Q_j(x)>0.
\tag{18}
$$

The reusable contraction theorem
`quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul`
starts from a separately supplied exact root against the prescribed payoff of
the semantic pair. The compact alternative
`exists_pos_exactRootOpponentAbsorptionFloor_of_no_soloExactRoot` concerns the
entire exact-root set at that payoff; (18) gives no information about it.

The preservation/restart half of the solo-wall file is even more specific.
`quittingTerminalSemanticDebt_prefix_solo_eq_of_uniqueDebtor` requires:

1. an exact solo root;
2. zero debt outside its solo owner; and
3. singleton tightness `U_j = r_j({j})`.

Our prescribed owner payoff is instead the mixed coalition reward `Q_j(x)`.
It need not equal the singleton reward. An exact root selected against the
source payoff may be all Continue, may use another owner, or may fail to have
an interior hazard. Therefore `exists_first_soloPrefix_outsiderWall` and the
finite-prefix solo-spine no-go do not follow from the pure-singleton source.

There is one valid conditional consequence. If no exact root against the
source payoff lies on `j`'s solo face, compactness supplies a positive
opponent-absorption floor. Prefixing by an exact root then strictly reduces
total carrier debt. This is an actual real-valued descent from the off-minimum
source, but it need not reach the minimum fiber in one step and supplies no
well-founded regeneration. It is not a complete consumer of the strict arm.

### Why the off-minimum charged-blocker gate does not apply

`exists_macroscopicDebtDrop_or_chargedSoloBlockerGate` takes a sequence of
carrier pairs and exact punishment-floor roots with one fixed positive
absorption floor. It then returns either positive liminf debt drop or a
quantitative solo blocker gate. The pure-singleton endpoint supplies none of
that root data:

* its displayed sure-owner root has the positive defect (18), hence is not
  exact;
* the source owner's payoff is not known to lie above its punishment floor;
  induced-game Nash gives the checked floor only for the three free players;
* arbitrary exact roots against the endpoint payoff need not have a positive
  uniform absorption floor; and
* no exact-root sequence or zero-drop subsequence is selected.

Even if those extra premises were produced, the charged-blocker theorem is a
further dispatch, not a final semantic consumer: its repayment arm still
controls a blocker coordinate and its updated tail is deliberately not a
carrier point.

### Redundancy with the existing singleton-base producer

At the table level the bare existence of a one-debtor sure-owner source is not
new. For every prescribed owner, the checked theorem

```text
FinFourQuantitativeFullSupportHardResidual
  .nonempty_singletonBaseSameLawResetProducer
```

in
`Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean` already
produces a stationary sure-owner source with:

* all free coordinates solved against unrestricted behavioral deviations;
* positive-debt support exactly the singleton owner;
* a full-gap paid row;
* a positive strict-superset terminal atom; and
* a same-law fixed-reset dispatch from a positive global minimum.

That checked producer is stronger than the bare one-active conclusion of
Section 1. The present arbitrary-tail calculation remains useful for auditing
the exact cap dependence on `B_j(Z)` and for showing that re-equilibration at
a specified literal tail need not move toward the minimum. But unless a
downstream theorem uses this tail attachment or the compact strict margin
`G_j(Z)-D_*`, the result does not create a genuinely smaller atlas node.

### Correct status

The equality arm remains a genuine conditional support-rank conclusion when
the retained source minimum has at least two debtors. The strict arm is an
exact source-local no-go for naive hazard interpolation, but it is currently
neither:

* consumed by the checked solo-wall/off-minimum gates; nor
* a strict new table-level producer beyond the existing singleton-base
  same-law reset source.

An export-worthy strengthening would have to use the additional fixed-tail
data to produce the exact roots, floor, and positive-charge chronology needed
by a checked consumer, or convert the uniform wall margin into one-step
minimum-fiber/support progress. Renaming the strict arm as a charged solo gate
would be mathematically false.
