# Unique-debtor floor entrance and solo recycling

Author: `CODEX_RAMSEY`

Status: **independently reviewed PASS**, with the four proof-writing handoffs
from
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE__BY_CODEX_EULER.md)
incorporated below.  This
note consumes the two explicit seams after the repaired codimension-one solo
carrier descent as far as the current source-native machinery permits.  It
produces a punishment-floor-safe unique-debtor carrier, then gives a precise
three-way recycle: a floor-preserving strict debt descent, a uniform payoff,
or the exact all-Continue stall.  The last wall is not claimed solved.

Input reviewed here:
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md),
Section 10, with the mandatory debt-localization repair recorded in
[`CODEX_RAMSEY__SECTION_10`](../feedback/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT__BY_CODEX_RAMSEY__SECTION_10.md).

The checked source-native solo machinery is in
`UniformEquilibrium/Diagnostics/Quitting/
TerminalSemanticFinFourSoloWallDispatch.lean`.

## 1. Repaired Section 10 input

Fix a Fin4 quitting reward table bounded by `M`, a terminal exploitability
witness with gap `gamma>0`, and its maintained quantitative full-support hard
residual.  In particular:

```text
0<gamma<=2M,
every player is punishment-normal,
for every owner e there is c!=e with
  r_c({e})+gamma <= r_c({e,c}).                         (1.1)
```

Write

```text
chi_i  = quittingPunishmentValue reward i,
solo_i = r_i({i}),
D_*    = the positive global minimum total semantic debt.
```

The repaired Theorem 10.1 supplies a carrier pair `R`, an owner `e`, and an
exact root at `R.1` such that

```text
d_i(R)=0  (i!=e),
d_e(R)>=gamma,
solo_e-R.1_e>=gamma,
D(R)>=D_*+gamma^2/(12M).                               (1.2)
```

The last root already gives a fixed carrier-debt drop, but its tail may be
below punishment and the singleton gap need not survive its successor.  The
argument below restarts from an arbitrary carrier with the first two fields,
using the *current floor deficit* instead of trying to preserve the original
gap.

## 2. Underfloor roots must expose an opponent

### Lemma 2.1 (floor-deficit opponent-absorption bound)

Let `X=(U,B)` be any Fin4 semantic carrier pair with unique possible debtor
`e`:

```text
d_i(X)=0 for i!=e.                                      (2.1)
```

Assume `e` is punishment-normal and has a full-gap singleton collider `c` as
in `(1.1)`.  If

```text
f = chi_e-U_e > 0                                      (2.2)
```

and `q` is any exact product Nash root against `U`, then

```text
A_{-e}(q) >= kappa(f) := min(f,gamma)/(12M)>0.          (2.3)
```

Here `A_{-e}` is the probability that at least one opponent of `e` Quits.

**Proof.**  Normality gives `solo_e>=chi_e`, hence at the all-Continue row

```text
QuitPayoff_e-ContinuePayoff_e = solo_e-U_e >= f.        (2.4)
```

Suppose `A_{-e}(q)<kappa(f)`.  Each of the three opponent Quit marginals is
at most this union probability.  Since a carrier prescribed coordinate is
an expectation of rewards, `|U_i|<=M`.  The checked opponent-TV stability
bound changes player `e`'s endpoint difference by less than

```text
4M*3*kappa(f) <= min(f,gamma) <= f.
```

Thus `e` strictly prefers Quit at `q`, and exact complementarity forces
`q_e=1`.

Compare now player `c` with the row where `e` Quits surely and the two labels
outside `{e,c}` Continue.  The `e` marginal agrees, so only two TV terms
remain.  By `(1.1)` the reference endpoint difference is at least `gamma`,
while the perturbation is strictly less than

```text
4M*2*kappa(f) <= 2gamma/3.
```

Hence `c` also strictly prefers Quit and exact complementarity forces
`q_c=1`.  This contradicts `A_{-e}(q)<kappa(f)<1`. `QED`

The constants deliberately use `12M` rather than optimize the second
comparison.  Since `gamma<=2M`, `kappa(f)<=1/6`.

### Corollary 2.2 (unique-debtor contraction while underfloor)

For `X'=Prefix(q,X)` under the hypotheses of Lemma 2.1,

```text
X' is in the same semantic carrier,
d_i(X')=0 for i!=e,
D(X') <= [1-kappa(f)]D(X).                              (2.5)
```

**Proof.**  Exact prefixing preserves the carrier and weakly decreases every
nonnegative debt coordinate, so the zero coordinates stay zero.  Apply
`quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul`
and `(2.3)`. `QED`

This replaces the nonpersistent initial solo gap by a persistent rule:
whenever the current unique debtor is below punishment, its current floor
deficit itself pays a quantitative contraction.

## 3. Floor entrance or a tight boundary carrier

Starting from `X_0=R`, recursively choose an exact root `q_n` against `X_n.1`
and set `X_(n+1)=Prefix(q_n,X_n)` for as long as
`X_n.1_e<chi_e`.  All pairs stay in the carrier, all non-`e` debts remain
zero, and `D(X_n)>=D_*>0`.

### Theorem 3.1 (floor entrance/tight-limit dichotomy)

This recursion has one of the following outcomes.

1. **Finite floor entrance.**  For some `N`,

   ```text
   chi_i<=X_N.1_i for every i.                           (3.1)
   ```

2. **Punishment-tight boundary.**  The recursion is infinite,

   ```text
   chi_e=solo_e,
   chi_e-X_n.1_e -> 0,                                  (3.2)
   ```

   and some subsequence converges to a carrier pair `Y` satisfying

   ```text
   chi_i<=Y.1_i for every i,
   Y.1_e=chi_e=solo_e,
   d_i(Y)=0 for i!=e,
   D(Y)>=D_*>0.                                         (3.3)
   ```

If the normality margin

```text
zeta_e=solo_e-chi_e
```

is positive, only finite floor entrance is possible.

**Proof.**  Let `f_n=chi_e-X_n.1_e>0` while the recursion continues.  For
every fixed `delta>0`, each index with `f_n>=delta` contracts total debt by
the fixed factor

```text
1-min(delta,gamma)/(12M) < 1.                           (3.4)
```

Debt is weakly decreasing at all other indices and remains at least `D_*`.
Therefore only finitely many indices can satisfy `f_n>=delta`; otherwise the
geometric bound would eventually put `D(X_n)` below `D_*`.  If the recursion
does not enter the floor, it follows that `f_n->0`.

If `zeta_e>0`, then `solo_e-X_n.1_e>=zeta_e` at every underfloor state.
Repeating the proof of Lemma 2.1 with `zeta_e` in place of `f_n` gives one
fixed positive contraction factor at *every* index, again contradicting the
positive minimum after sufficiently many steps.  Thus entrance is finite.

In the infinite case, `f_n->0` and normality force no more than
`chi_e<=solo_e`; to get the asserted equality, observe that a strict margin
would be the preceding finite-entrance case.  Compactness of the semantic
carrier gives a convergent subsequence.  Its `e` prescribed coordinate tends
to `chi_e`, the zero-debt coordinates remain zero, and total debt is bounded
below by `D_*`, proving `(3.3)`.  For `i!=e`, zero debt gives `U_i=B_i`, and
every behavioral cap is at least the punishment value; this inequality passes
to the carrier limit. `QED`

Thus Section 10's source always yields a floor-safe unique-debtor carrier: a
finite exact semantic prefix in the strict-normal arm, or a carrier limit in
the punishment-tight arm.  Neither phrase asserts literal realization by one
behavior profile: the Section 10 source itself is a compactified conditional
suffix, and `Prefix` is used here at the semantic-carrier level.

There is one additional useful fact in the infinite branch.  Write
`A_n=A_{-e}(q_n)`.  Iterating the unique-debtor contraction gives

```text
D_* <= D(X_N) <= D(X_0) * product_{n<N}(1-A_n).         (3.5)
```

Consequently `sum_n A_n<infinity`, in particular `A_n->0`.  After refining
the compact subsequence jointly in the roots, the limiting root is exact
against `Y.1` and all opponents of `e` Continue.  Thus the tight-limit output
automatically has a solo-face exact root.  This observation is not needed for
the general recycle below, but rules out its no-solo branch at that particular
limit.

For completeness, the product-to-sum implication uses no hidden attainment:
`0<=A_n<1` and `1-A_n<=exp(-A_n)`, while `(3.5)` bounds every finite product
below by `D_*/D(X_0)>0`.  Hence every partial sum of the nonnegative `A_n` is
at most `log(D(X_0)/D_*)`, which proves summability.

## 4. Recycling the floor-safe carrier

Let `Y` denote either floor-safe output of Theorem 3.1.  Consider exact roots
against `Y.1` whose opponents of `e` all Continue; call these **solo-face
roots**.  A solo-face root has only `e` possibly Quit.

### Theorem 4.1 (adaptive floor-safe recycle trichotomy)

From `Y`, at least one of the following holds.

1. **Floor-preserving strict debt descent.**  There are an exact root and
   `Y'=Prefix(q,Y)` such that every coordinate of `Y'.1` is above punishment
   and

   ```text
   D(Y') <= D(Y)-omega D(Y) < D(Y)                     (4.1)
   ```

   for some source-specific `omega>0`.

2. **Uniform payoff.**  The same table admits a uniform-equilibrium payoff.

3. **Positive-debt all-Continue stall.**  There is a floor-safe carrier `Z`
   with the same debt vector as `Y` such that all Continue is an exact root at
   `Z.1`.  In particular `D(Z)=D(Y)>=D_*>0`; this is not a solved branch.

**Proof.**  Apply the following recycling rule at a floor-safe carrier `X`
with the same unique-debtor debt vector as `Y`.

- If all Continue is exact at `X.1`, stop in arm 3.
- If no solo-face exact root exists, compactness of the exact-root set and
  `exists_pos_exactRootOpponentAbsorptionFloor_of_no_soloExactRoot` give
  `omega>0` such that every exact root has `A_{-e}>=omega`.  The checked
  `exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor` gives arm 1.
- Otherwise choose a solo-face exact root.  Since all Continue was excluded,
  its owner Quit probability `p` is positive.  It is strictly below one:
  if `p=1`, the collider `c` from `(1.1)` has endpoint difference at least
  `gamma` and cannot Continue in an exact root.  Exact owner complementarity
  gives `X.1_e=solo_e`.  Because all opponents are pure Continue, extensionality
  rewrites this arbitrary root exactly as

  ```text
  q = quittingSoloStationaryRoot e (q e).
  ```

  Set `X'=Prefix(q,X)` and repeat.

The third rule preserves every debt coordinate by
`quittingTerminalSemanticDebt_prefix_solo_eq_of_uniqueDebtor`; it preserves
the punishment floor by
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge`; and it preserves
singleton tightness because

```text
X'.1_e=(1-p)X.1_e+p solo_e=solo_e.                    (4.2)
```

Dependent choice therefore either stops in arm 1 or 3, or produces an
infinite exact punishment-floor orbit `(X_n,q_n)` of solo roots with

```text
0<p_n<1,
charge(q_n)=p_n,
d_i(X_n)=d_i(Y) for every i,n.                         (4.3)
```

If `sum_n p_n` is not summable, apply the checked theorem
`QuittingPunishmentFloorInfiniteOrbit.
exists_uniformEquilibriumPayoff_of_not_summable_absorption`, because a solo
root's total absorption mass is exactly `p_n`.  More explicitly, package the
sequence as a `QuittingPunishmentFloorInfiniteOrbit` with

```text
roots n       = q_n,
value n       = X_n.1,
value_mem     = carrier reward-box membership,
anchor_floor  = floor safety of X_0,
policy        = X_(n+1).1=Succ(X_n.1,q_n),
exactNash     = the selected exact solo-root property.                (4.4)
```

This is the forward Bellman orientation; it does not reverse the behavioral
prefix chronology.  Applying the checked nonsummable-charge theorem gives
arm 2.

If `sum_n p_n` is summable, then `p_n->0`.  The semantic prefix identity gives

```text
|X_(n+1).1_i-X_n.1_i| <= 2M p_n,                      (4.5)
```

so the prescribed vectors converge coordinatewise.  Since the debt vector
is constant, the identity

```text
X_n.2_i = X_n.1_i + d_i(Y)                            (4.6)
```

makes the envelope vectors converge as well; write the pair limit as `Z`.
Closedness of the semantic carrier puts `Z` back in the carrier.  The solo
roots converge to all Continue.  Closedness of the exact-root graph makes all
Continue exact against `Z.1`, while closedness of the floor preserves the
remaining fields.  This is arm 3. `QED`

If the floor entrance in Theorem 3.1 stopped with `Y.1_e!=solo_e`, then either
all Continue is already exact or no solo-face exact root exists: a genuinely
mixed solo root requires owner indifference, and a sure-Quit solo root is
excluded by the collider.  Thus the adaptive part is only needed on the
singleton-tight face.

## 5. What this resolves and what remains

The construction does not assume that the initial gap
`solo_e-R.1_e>=gamma` survives.  It replaces that unavailable invariant by
the current punishment-floor deficit and consumes it quantitatively.  Hence
the two Section 10 seams reduce to one exact wall:

```text
(a) a floor-safe all-Continue exact carrier with one positive debtor. (5.1)
```

Outside this wall the result supplies either a floor-preserving strict
carrier-debt decrease or a uniform-equilibrium payoff.  The recycling is
adaptive: it does not assume that one initially selected solo root remains
exact after prefixing.

This is not yet a complete well-founded induction.  The strict debt descent
in arm 1 is source-specific; its opponent-absorption constant need not persist
after the step.  Arm 3 is exactly the previously identified all-Continue
semantic stall.  No claim is made that a single strict real-valued debt
decrease is a finite rank.

The local nature of this final wall is sharp.  The literal Fin4 regression in
[`CODEX_MINER__FIN4_SINGLETON_BASE_ALLCONTINUE_RESET_WALL.md`](CODEX_MINER__FIN4_SINGLETON_BASE_ALLCONTINUE_RESET_WALL.md)
has a floor-safe positive-debt carrier at which all Continue is exact, even
while retaining the exposed same-law paid/reset fields.  That regression
deliberately lacks the ambient terminal witness and positive-global-minimum
hypotheses.  Thus eliminating `(5.1)` must use those ambient hypotheses; the
carrier, normality, collider, and floor fields used above do not suffice by
themselves.

## 6. Source/novelty boundary and review request

The following ingredients are already checked:

- `finFourExactRootSet_isCompact` and
  `exists_pos_exactRootOpponentAbsorptionFloor_of_no_soloExactRoot`;
- `quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul`;
- `quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` and
  `exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor`;
- `quittingTerminalSemanticDebt_prefix_solo_eq_of_uniqueDebtor`; and
- `QuittingPunishmentFloorInfiniteOrbit.
  exists_uniformEquilibriumPayoff_of_not_summable_absorption`.

The first four are in
`TerminalSemanticFinFourSoloWallDispatch.lean` (with the floor-forward lemma
imported there); the last is in
`PunishmentFloorInfiniteOrbitChargeDichotomy.lean`.  The nearby checked
`exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower` assumes
a fixed minimum semantic spine in the opposite indexing convention.  It does
not supply the underfloor entrance or the adaptive forward recycle from this
off-minimum Section 10 carrier.

The new ordinary-mathematics content is the adapter from the repaired
Section 10 conditional suffix to the quantitative floor-deficit recursion,
the finite strict-normal entrance, and the tight-limit/floor-recycle
composition.  It is not a new general supplied-object verifier.

Please independently falsify:

1. Lemma 2.1's TV constants and use of the current floor deficit;
2. the geometric count proving finite strict-normal entrance and
   `f_n->0` in the tight branch;
3. the claim that all nondebtor coordinates are automatically floor-safe;
4. the adaptive solo-root recursion, including the summable/nonsummable split;
   and
5. the exact nonclaims about regeneration, well-founded rank, and the
   all-Continue stall.
