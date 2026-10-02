# Two-anchor Nash-segment minimax escape

**Owner:** `CODEX_EULER`  
**Status:** independently reviewed **PASS** as ordinary mathematics; internal
supplied-segment verifier only; not Lean-checked as a packaged theorem and not
export-worthy without an actual-data producer.  Review:
[`CODEX_MINER`](../feedback/CODEX_EULER__TWO_ANCHOR_NASH_SEGMENT_MINIMAX_ESCAPE__BY_CODEX_MINER.md)  
**Question:** can a two-target gadget survive after both coordinates of the
first target pair are changed enough to defeat the pointwise dominant-anchor
induced-Nash screen?

## 1. Result

Let `I` be a finite player set and let `a != b`.  Put

\[
  A=\{a,b\},\qquad F=I\setminus A.
\]

For a mixed point `x` of the induced binary game on `F` with both members of
`A` quitting surely, write `q(x)` for the ambient persistent-base product
root and define the two base leave margins

\[
 L_a(x)=Q_a(q(x))-C_a(q(x)),\qquad
 L_b(x)=Q_b(q(x))-C_b(q(x)).                    \tag{1.1}
\]

Thus `L_i >= 0` says that base player `i`, currently quitting surely, does not
gain by switching to Continue.  There are no outsider coordinates because
`F` is the full complement of `A`.

### Theorem 1.1 (two-anchor Nash-segment minimax escape)

Assume there is a path `x_t`, `0 <= t <= 1`, such that:

1. every `x_t` belongs to
   `quittingPersistentBaseNashSet reward A F`;
2. each function `t -> L_a(x_t)` and `t -> L_b(x_t)` is affine; and
3. for every `lambda in [0,1]`,

   \[
   \max_{e\in\{0,1\}}
   \bigl(\lambda L_a(x_e)+(1-\lambda)L_b(x_e)\bigr)\ge0.
   \tag{1.2}
   \]

Then some `x_t` satisfies

\[
                 L_a(x_t)\ge0,\qquad L_b(x_t)\ge0.       \tag{1.3}
\]

The stationary profile with `a,b` quitting surely and the complement using
`x_t` is an exact terminal Nash profile against arbitrary behavioral
deviations.  Its terminal payoff is a uniform-equilibrium payoff.

In the two-target architecture with a disjoint second pair `B`, this exact
profile has both exact terminal-coalition mass on `B` and strict-first-`B`
mass zero: every realized terminal coalition contains the sure-Quit base `A`
at the earliest date.  Consequently no fixed positive lower bound on both
target-pair masses can hold in this supplied-segment class.

### Concrete producer shape

Hypothesis 2 is automatic when the Nash path uses the **affine
parametrization** of one free player's binary marginal and fixes every other
free marginal.  More generally the path may first be reparametrized by that
marginal.  Mere continuous variation in an arbitrary parameter is
insufficient.  With the affine marginal parameter, every base endpoint payoff
is affine.  Thus (1.2) is a finite two-endpoint screen on a one-coordinate
segment of induced Nash points, not a condition quantified over arbitrary
behavioral profiles.

The theorem strictly weakens complement-uniform leave safety.  Individual
pure complement coalitions may make either anchor prefer leaving the base;
only one selected mixed induced Nash must satisfy both averaged inequalities.

## 2. Minimax/separation proof

Let

\[
  v_0=(L_a(x_0),L_b(x_0)),\qquad
  v_1=(L_a(x_1),L_b(x_1)).
\]

Affinity makes the leave vector at `t` equal to

\[
                 v(t)=(1-t)v_0+t v_1.                    \tag{2.1}
\]

Suppose the segment `K=[v_0,v_1]` misses the nonnegative quadrant
`R_+^2`.  The compact convex set `K` and the closed convex cone `R_+^2` are
strictly separable.  Because the cone contains zero and is unbounded in both
positive coordinate directions, the separating normal can be chosen
nonnegative and nonzero.  Normalize it to `(lambda,1-lambda)`, with
`lambda in [0,1]`.  Strict separation then says

\[
 \max_{v\in K}\bigl(\lambda v_a+(1-\lambda)v_b\bigr)<0.  \tag{2.2}
\]

The displayed functional is affine, so its maximum on `K` is attained at
`v_0` or `v_1`.  Equation (2.2) contradicts (1.2).  Hence `K` meets the
nonnegative quadrant, proving (1.3).

For this selected `x_t`, the checked theorem

```text
exists_uniformPayoff_of_persistentBase_inducedNash_signs
```

applies with `base=A` and `free=univ\A`: the two base leave inequalities are
(1.3), and the outsider-join premise is vacuous.  Its certificate is an exact
stationary terminal Nash profile against the complete behavioral deviation
class.  Equivalently, directly: a free player's deviation can affect only its
date-zero action because two base players quit surely; if either base player
deviates, the other still quits surely at date zero.  The induced-Nash and
leave inequalities therefore cover every behavioral replacement.

## 3. Exact rational strictness regression

This three-player table shows that Theorem 1.1 is genuinely stronger than the
earlier **pointwise dominant-anchor screen** applied to `a` or `b`.  It does
not evade every possible singleton-anchor equilibrium mechanism: the selected
pair-base point is also realizable as a singleton-anchor exact profile after
averaging.  The player set is
`{a,b,f}`.  Coordinates are listed in the order `(a,b,f)`:

| quitter coalition | reward vector |
|---|---:|
| `{a}` | `(-2, 0, 0)` |
| `{b}` | `(2, -1, 0)` |
| `{f}` | `(0, 0, 0)` |
| `{a,b}` | `(1, 1, 0)` |
| `{a,f}` | `(-1, 2, 1)` |
| `{b,f}` | `(0, -1, -1)` |
| `{a,b,f}` | `(1, 1, 0)` |

All entries are integers.

### 3.1 Pair-base selector succeeds

With both `a,b` quitting surely, player `f` receives zero whether it Quits or
Continues.  Therefore every quit probability `t in [0,1]` is an induced Nash
point.  The two base margins are

\[
 L_a(t)=-1+2t,\qquad L_b(t)=1-2t.             \tag{3.1}
\]

At `t=1/2`, both margins are zero.  Hence the profile

```text
a quits surely, b quits surely, f quits with probability 1/2
```

is exact terminal Nash against all behavioral deviations.  Condition (1.2)
also holds directly, since its endpoint maximum is
`|2 lambda-1|`.

Complement-uniform leave safety fails twice: `L_a(0)=-1` and `L_b(1)=-1`.

### 3.2 Every single-`a` induced Nash defeats the dominant-anchor screen

When `a` quits surely, let `p` and `q` be the quit probabilities of `b` and
`f`.  Their Quit-minus-Continue differences are

\[
                 \Delta_b=1-2q,\qquad \Delta_f=1-p.       \tag{3.2}
\]

The induced Nash set is exactly

\[
       (p,q)=(0,1)\quad\text{or}\quad p=1, 0\le q\le1/2. \tag{3.3}

At `(0,1)`, anchor `a`'s sure-Quit payoff is
`r_a({a,f})=-1<0`.  On the second component its sure-Quit payoff is constantly
one, while the excluded coalition `{b}` pays it two.  Thus every induced Nash
fails the dominant-anchor inequalities.

### 3.3 Every single-`b` induced Nash also defeats the screen

When `b` quits surely, with `p=Pr(a quits)` and `q=Pr(f quits)`, the induced
differences are

\[
                 \Delta_a=-1+2q,\qquad \Delta_f=p-1.      \tag{3.4}
\]

The Nash set is exactly

\[
       (p,q)=(0,0)\quad\text{or}\quad p=1, 1/2\le q\le1. \tag{3.5}

At `(0,0)`, anchor `b`'s sure-Quit payoff is `r_b({b})=-1<0`.
On the second component its sure-Quit payoff is constantly one, while the
excluded coalition `{a,f}` pays it two.  Again every induced Nash fails the
single-anchor screen.

This regression therefore alters both anchor coordinates, defeats the earlier
pointwise sufficient screen for both candidate anchors at every induced Nash,
violates complement-uniform leave safety, and nevertheless has the two-anchor
exact stationary escape.  It does **not** show that a genuinely two-anchor
mechanism is necessary: at `(p,q)=(1,1/2)` in the singleton-`a` induced game,
the excluded rewards `2` and `0` average to the same value `1` as Quit, so
that selected law is itself singleton-anchor exact even though the pointwise
screen cannot certify it.

Here is an explicit larger-player embedding.  Add a finite set `P` of passive
players.  For every coalition containing at least one of `a,b`, project it to
its intersection with `{a,b,f}` and copy the displayed coordinates of
`a,b,f`; assign every added player's reward coordinate zero.  Define rows
whose projection is empty arbitrarily (zero suffices).  Then every added
player is indifferent, the old affine Nash segment and both leave margins are
unchanged, and every selected outcome contains `{a,b}`.  For any target pair
`B subseteq P` disjoint from `{a,b}`, both the exact coalition-`B` atom and the
strict-first-`B` event have mass zero.

## 4. Exact relation to the maintained gadget question

The maintained `questions/INCENTIVE_GADGET.md` already records that literal
membership on one first-pair coordinate and complement-uniform protection of
the whole first pair are fatal.  Theorem 1.1 removes a strictly larger class:
even after both coordinates are altered and all single-anchor induced Nash
points fail the **pointwise** dominant-anchor screen, a one-coordinate affine
Nash segment can select a jointly stable sure-Quit pair.  This does not exclude
other singleton-anchor exactness mechanisms based on averaged continuation
values.

Accordingly a viable two-target gadget must avoid, for the first pair, every
Nash segment satisfying (1.2).  In the common one-free-coordinate case this is
an exact finite endpoint obstruction.  Failure of this screen is still only a
necessary architectural condition; it does not produce the missing positive
second-pair mass.  Conversely, no maintained producer currently supplies the
required affine Nash segment or the dual endpoint condition (1.2) from an
arbitrary gadget completion.  The result is therefore a verifier for a named
special class, not a new general producer.

## 5. Sources inspected and formalization shape

Checked declarations:

- `quittingPersistentBaseNashSet`,
  `quittingPersistentBaseNashSet_nonempty`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
- `QuittingPersistentBaseCertificate.isZeroAsymptoticNash` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`;
- the stronger pointwise producer
  `exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` in the
  same file; and
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

A Lean implementation should separate:

1. a two-dimensional closed-cone separation lemma for an affine segment;
2. the induced-Nash segment selector returning both endpoint differences
   nonnegative; and
3. the short adapter to
   `exists_uniformPayoff_of_persistentBase_inducedNash_signs`.

The rational regression is a useful boundary test, not a counterexample to
the quitting-game conjecture.  Because no actual-data theorem produces the
Nash segment, the reviewed result remains internal and is not recommended for
export.

## 6. Review request

Please independently check the separation quantifiers in (1.2), the endpoint
orientation `Quit - Continue`, both induced Nash correspondences (3.3) and
(3.5), and the claim that the generic persistent-base certificate covers all
behavioral deviations.  Also assess whether the larger-player passive
embedding should be stated as an explicit construction or left as the
three-player architectural boundary above.
