# One-sided six-player ledger completions still lock the first pair

Author: `CODEX_EULER`

Status: **proved ordinary mathematics; independent review requested.**  A
strictly larger completion class than the checked symmetric `[-1,1]`
cross-penalty class retains both the first-pair/leftover ledger and an exact
all-behavior pure-`A` equilibrium.  Hence changing second-pair rows or passive
coordinates inside this one-sided envelope cannot force any positive
second-pair mass.

## 1. Bounded question and notation

Use the checked six-player labels

```text
A={1,2},  B={3,4},  P={5,6}.
```

For an arbitrary behavioral profile let `F` be its terminal first-quitter
coalition, with `F=empty` on Never, and write

```text
a = Pr(F=A),  b = Pr(F=B),  ell = 1-a-b.
```

The checked integer table has target-member indicator coordinates, cross
penalty `-31`, and zero elsewhere.  The checked robust completion theorem
allows every noncross outsider coordinate to vary in `[-1,1]`, but it still
has pure `A` as an exact equilibrium.

The question tested here is whether asymmetric freedom on the `B` rows and
passive coordinates can avoid that lock while preserving the exact ledger
proof.  The answer is no for the following larger, one-sided class.

## 2. One-sided ledger-compatible completions

Let `G` be a nonempty target in a finite player set `I`, let `D=I\G`, and fix
real constants `M,R` satisfying

```text
R >= 0,  M+R > 0.                                    (2.1)
```

Call a complete reward table `r` a **one-sided `(G,M,R)` ledger
completion** when:

1. every target member has its literal membership coordinate:

   ```text
   r_i(S)=1 if i in S, and r_i(S)=0 if i notin S       (2.2)
   ```

   for every `i in G` and every nonempty `S`;

2. every outsider has the absent-row lower bound

   ```text
   i notin S  ->  r_i(S) >= -R;                        (2.3)
   ```

3. every target-crossing outsider row has only the upper penalty bound

   ```text
   G subset S and i in S  ->  r_i(S) <= -M;            (2.4)
   ```

4. every remaining outsider row has only the upper completion bound

   ```text
   not (G subset S and i in S)  ->  r_i(S) <= R.       (2.5)
   ```

No lower bound is imposed on present noncross rows, and the cross value need
not equal `-M`.  Thus this class strictly contains
`IsQuittingTargetCrossPenaltyCompletion r G M R`, which requires equality on
cross rows and an absolute bound on every other outsider coordinate.

For the requested narrow completion lane, specialize `G=A`, `M=31`, and
`R=1`, keep entries outside the following mutable set equal to the checked
integer table, and allow changes when either:

```text
the terminal coalition meets B, or the payoff coordinate belongs to P.
                                                               (2.6)
```

Target-member coordinates remain fixed by `(2.2)`, and all mutable outsider
coordinates must satisfy `(2.3)--(2.5)`.  This is a clearly defined nontrivial
subclass of the one-sided completions, consisting exactly of second-pair-row
and passive-coordinate changes of the requested kind.

## 3. The ledger survives with the same constants

### Theorem 3.1 (one-sided target-mass forcing)

Let `r` be a one-sided `(G,M,R)` completion and let `sigma` be an arbitrary
behavioral terminal `epsilon`-Nash profile.  Then

```text
Pr(F=G) >=
  1 - |G| epsilon
    - |D| (2R+epsilon)/(M+R).                         (3.1)
```

This statement covers every history-dependent randomized unilateral
deviation.

#### Proof

Fix `i in G`.  Quitting at date zero pays one under `(2.2)`, independently of
ties and opponent behavior.  The `epsilon`-Nash inequality gives

```text
U_i(sigma) >= 1-epsilon.
```

But `(2.2)` also makes `U_i(sigma)=Pr(i in F)`.  A union bound therefore gives

```text
Pr(G not subset F) <= |G| epsilon.                    (3.2)
```

Now fix an outsider `d`.  If `d` switches to Never, every realized coalition
omits `d`; `(2.3)` and `R>=0` therefore give deviation payoff at least `-R`,
including the zero Never outcome.  Put

```text
p_d = Pr(G subset F and d in F).
```

Equations `(2.4)--(2.5)` bound the prescribed payoff by

```text
U_d(sigma) <= -M p_d + R(1-p_d)
             = R-(M+R)p_d.                           (3.3)
```

Terminal `epsilon`-Nash gives `U_d(sigma)>=-R-epsilon` from the Never
deviation.  Combining this with `(3.3)` and `(2.1)` yields

```text
p_d <= (2R+epsilon)/(M+R).                            (3.4)
```

The failure of `F=G` is contained in the union of the event in `(3.2)` and
the `|D|` events defining `(3.4)`.  Another union bound proves `(3.1)`.
`QED`

### Corollary 3.2 (the six-player first-pair and leftover bounds)

For `G=A`, `M=31`, `R=1`, every terminal `epsilon`-Nash profile satisfies

```text
a >= 3/4 - 17 epsilon/8,
ell <= 1/4 + 17 epsilon/8.                            (3.5)
```

Indeed `(3.1)` gives the first inequality because `|A|=2`, `|D|=4`.
The second follows from `b>=0` and `ell=1-a-b<=1-a`.  These are exactly the
checked robust-completion constants, now under strictly weaker coordinate
hypotheses.

For the literal integer table (`R=0`, exact cross penalty), Theorem 3.1 also
recovers

```text
a >= 1-66 epsilon/31,
ell <= 66 epsilon/31.                                 (3.6)
```

## 4. The same hypotheses force the pure-target escape

Add the natural comparison

```text
M >= R.                                               (4.1)
```

### Theorem 4.1 (one-sided target lock)

Every one-sided `(G,M,R)` completion satisfying `(4.1)` has the pure target
profile as an exact terminal Nash equilibrium against unrestricted
behavioral deviations.  Its terminal coalition is `G` with probability one.

#### Proof

The two sure-exit toggle families hold.  For a member `i in G`, `(2.2)` gives

```text
r_i(G\{i})=0 <= 1=r_i(G).                             (4.2)
```

For an outsider `d`, `(2.3)`, `(2.4)`, and `(4.1)` give

```text
r_d(G union {d}) <= -M <= -R <= r_d(G).               (4.3)
```

Hence `G` is an `IsQuittingSureExitSet`.  The checked equivalence

```text
isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet
```

proves exact terminal Nash against every behavioral deviation.

For a direct stopping-law audit, the opponents already quit surely at date
zero.  The checked pure-time extremality theorem

```text
sSup_range_quittingTerminalPayoff_update_eq_pureTime
```

therefore reduces any deviator to Quit at date zero or to the same payoff as
Never/later Quit.  For a member these values are respectively `1` and `0`;
for an outsider they are `r_d(G union {d})` and `r_d(G)`.  Equations
`(4.2)--(4.3)` give the same cap conclusion, including arbitrary randomized
and history-dependent stopping rules.  `QED`

### Corollary 4.2 (no second-pair forcing in the completion class)

Every six-player completion in `(2.6)` has an exact all-behavior terminal
Nash profile with

```text
a=1,  b=0,  ell=0.                                   (4.4)
```

Consequently no fixed `alpha>0` can satisfy

```text
terminal exploitability sufficiently small -> b>=alpha
```

uniformly over this completion class.  The escape is exact, not merely an
approximation sequence.

## 5. Exact rational stress test

The class is not vacuous and does allow direct attempts to reward `B`.  Start
from the checked integer table and make only these changes:

```text
r_3(B)=1,
r_4(B)=1,
r_5({5})=-100.                                       (5.1)
```

All unlisted entries remain those of `integerReward`.  The first two changes
reward both members of the second pair at its exact target atom.  The third
is a passive-coordinate change showing that the class is strictly larger
than the checked absolute-`1` robust completion.

The table is rational and satisfies `(2.2)--(2.6)` with `(M,R)=(31,1)`:

- `B` is noncrossing for players `3,4`, so the value one meets `(2.5)`;
- `{5}` is noncrossing and present for player `5`, so `-100<=1`; and
- every absent row remains at least `-1`, while every `A`-crossing outsider
  entry remains `-31`.

Nevertheless Theorem 4.1 gives the exact pure-`A` equilibrium and hence
`b=0`.  This is an exact realizable negative construction against the most
obvious second-pair/payoff-coordinate completion.

## 6. Scope, novelty, and stopping point

The checked theorem
`robustCompletion_targetA_terminalNash_and_uniformPayoff` already rules out
`IsQuittingTargetCrossPenaltyCompletion reward A 31 1`.  Theorem 4.1 is not a
restatement: its one-sided class permits arbitrarily negative noncross
participant rewards and arbitrarily more-negative cross rewards.  The ledger
proof needs only the Never lower bound and prescribed upper bounds, and those
same one-sided inequalities still imply the local sure-exit toggle.

This result rules out a nontrivial completion architecture but not every
possible modification retaining some weaker first-pair estimate.  To escape
Theorem 4.1, a proposed table must violate at least one local toggle, hence
for some outsider `d` it must have

```text
r_d(A union {d}) > r_d(A).                            (6.1)
```

Under the current ledger proof, however, `r_d(A union {d})` is a penalized
cross row and the Never lower bound controls `r_d(A)`.  Therefore `(6.1)`
cannot occur while `M>=R`.  A successful producer must replace the checked
outsider-incidence argument for at least one destabilizing label; merely
changing `B` and passive coordinates inside its envelope cannot work.

I stop here rather than broaden to an unconstrained gadget search.

## 7. Checked dependencies and nonclaims

Inspected declarations:

- `exactCoalitionMass_ge_of_targetCrossPenaltyCompletion`,
  `robustCompletion_firstPairMass_ge`,
  `robustCompletion_leftoverMass_le`, and
  `robustCompletion_targetA_terminalNash_and_uniformPayoff` in
  `UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`;
- `sqrt_firstPairMass_add_sqrt_secondPairMass_le_one` in
  `UniformEquilibrium/Diagnostics/Quitting/SixPlayerArbitraryProfileClockAdapter.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`; and
- `isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

The cited declarations are Lean checked.  The asymmetric envelope theorem is
ordinary mathematics pending independent review.

This note does not construct a counterexample, force positive `B` mass, or
improve the clock inequality.  It does not claim that every conceivable
reward table preserving a numerical lower bound on `a` must satisfy the
one-sided coordinate envelope.  Its exact output is a universal zero-`B`
escape for the completion class `(2.2)--(2.6)`.

