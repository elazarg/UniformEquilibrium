# Large persistent-base finite Nash dispatch

Authors: CODEX_EULER

Independent review:
[CODEX_RAMSEY](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_26_1.md)

## Exact statement

Let `I` be a four-element player set and let a quitting reward table be fixed.
Suppose `B,F subset I` are disjoint, `|B|>=2`, and `|F|>=2`.  For each subset
`R subset F`, regard `B union R` as the date-zero quitting coalition.  The
players in `F` thereby face a finite binary-action game: `Quit` means
membership in `R` and `Continue` means nonmembership.

For a product mixed Nash equilibrium `p` of this induced game and `c in B`,
define the base-leave gain

```text
L_c(p)
 = E_p[r_((B\{c}) union R)(c)-r_(B union R)(c)].    (1)
```

Assume that a supplied `gamma>0` satisfies

```text
forall induced Nash equilibria p,
max_(c in B) L_c(p) >= gamma.                       (2)
```

Then `|B|=|F|=2` and `I=B disjoint-union F`.  Write

```text
B={a,b},        F={x,y}.
```

Encode Continue by `0` and Quit by `1`.  Set

```text
C_ij = B union ({x} if i=1) union ({y} if j=1),
X_ij = r_(C_ij)(x),              Y_ij = r_(C_ij)(y),

alpha_j = X_1j-X_0j,             beta_i = Y_i1-Y_i0,
ell_c^ij = r_(C_ij\{c})(c)-r_(C_ij)(c).             (3)
```

Exactly one of the following two alternatives holds.

1. There are `i,j in {0,1}` and `c in B` such that `(i,j)` is a pure
   induced Nash cell and

   ```text
   ell_c^ij >= gamma.                               (4)
   ```

   Explicitly, the pure best-response conditions are

   ```text
   i=0 -> alpha_j<=0,       i=1 -> alpha_j>=0,
   j=0 -> beta_i <=0,       j=1 -> beta_i >=0.       (5)
   ```

2. There is no pure induced Nash cell.  The payoff differences have exactly
   one of the two strict matching-pennies orientations

   ```text
   alpha_0>0>alpha_1,       beta_1>0>beta_0,         (6+)
   alpha_1>0>alpha_0,       beta_0>0>beta_1.         (6-)
   ```

   The induced game has one Nash equilibrium, and it is fully mixed.  Put

   ```text
   D=(alpha_0-alpha_1)(beta_1-beta_0)>0,

   N_c=(-beta_1 alpha_1) ell_c^00
       +( beta_0 alpha_1) ell_c^10
       +( beta_1 alpha_0) ell_c^01
       +(-beta_0 alpha_0) ell_c^11.                 (7)
   ```

   Then some `c in B` satisfies the division-free polynomial inequality

   ```text
   N_c >= gamma D > 0.                              (8)
   ```

   The unique mixed rates and their product weights are

   ```text
   s=Pr(x Quits)=-beta_0/(beta_1-beta_0),
   t=Pr(y Quits)= alpha_0/(alpha_0-alpha_1),          (9)

   Pr(0,0)=(-beta_1 alpha_1)/D,
   Pr(1,0)=( beta_0 alpha_1)/D,
   Pr(0,1)=( beta_1 alpha_0)/D,
   Pr(1,1)=(-beta_0 alpha_0)/D.                     (10)
   ```

Thus the continuum-quantified large-base residual (2) is replaced by eight
possible pure paid-leave certificates, or by two strict matching-pennies sign
orientations with one of two polynomial paid-leave inequalities.

The mixed alternative has the following additional exact dispatch.  Choose
`c in B` satisfying (8), write `B={c,d}`, and define the base-deleted square

```text
D_ij={d} union ({x} if i=1) union ({y} if j=1),

bar_alpha_j=r_(D_1j)(x)-r_(D_0j)(x),
bar_beta_i =r_(D_i1)(y)-r_(D_i0)(y),

R_x=-alpha_1 bar_alpha_0+alpha_0 bar_alpha_1,
R_y= beta_1 bar_beta_0-beta_0 bar_beta_1.            (11)
```

Let the positive cleared weights be

```text
W_00=-beta_1 alpha_1,       W_10= beta_0 alpha_1,
W_01= beta_1 alpha_0,       W_11=-beta_0 alpha_0,
sum W_ij=D,                                             (12)
```

and let `chi_d` be player `d`'s punishment value.  Define

```text
K_d=W_00 chi_d+W_10 r_{x}(d)+W_01 r_{y}(d)+W_11 r_{x,y}(d)
    -sum_(i,j) W_ij r_(D_ij)(d).                       (13)
```

If

```text
R_x=0,                R_y=0,                K_d<=0,    (14)
```

then the root at which `d` Quits surely, `x,y` use the same mixed rates as in
(9), and `c` Continues is accepted by the checked singleton-base
all-behavior compiler.  Hence, under a terminal exploitability witness, every
mixed output further satisfies the strictly smaller polynomial/punishment
residual

```text
R_x != 0       or       R_y != 0       or       K_d>0. (15)
```

## Conjecture-facing change

The maintained question is
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
Its checked support-two route now reaches a strict-toggle semantic dispatch.
The live large-persistent-base arm says that the concrete excess `G` is
uniformly positive on the complete induced Nash set.  Statement (2) is
exactly that arm after the four-player cardinality collapse: there are no
outside players, and the components of `G` indexed by free players are zero
on the induced Nash set.

The theorem strictly narrows this obligation.  It removes both the compact
Nash-set quantifier and all selected real rates.  Its outputs are finite
sign/equality cells and division-free polynomial inequalities in pair,
triple, and grand-coalition rewards.  The pure output also identifies an
internally stable source coalition with a quantitatively paid base-leave
toggle.

The pure output is not consumed.  In the mixed output, however, (11)--(14)
give an exact handoff to the existing singleton-base compiler.  If that
handoff fails, (15) records exactly two base-deletion reprojection seams or
one punishment-priced owner premium.  A paid base leave is precisely why the
original two-member sure-base root fails, but after deleting that member it
becomes the required strict outsider no-join inequality.

## Definitions and assumptions

At one live date, each player independently randomizes between Quit and
Continue.  The first nonempty quitting coalition absorbs.  In the induced
game the two players in `B` Quit surely and the two players in `F` use their
ordinary independent mixed actions.  Because another member of `B` remains
after any one base member leaves, every payoff in (1) is attached to a
nonempty coalition.

The theorem itself is finite normal-form algebra.  It does not restrict an
eventual unilateral deviator to stationary or bounded-memory strategies,
because it asserts no equilibrium of the infinite quitting game.  Its source
hypothesis is nevertheless the literal `G` residual of the checked
all-behavior semantic dispatch.  In the successful `G<=0` branch, the checked
persistent-base compiler covers unrestricted behavioral deviations: after
one free player or one base player deviates, another base member still Quits
surely, so only the deviator's date-zero membership choice affects the
terminal coalition.

No public correlation or mixed stopping-law correlation is used.  The mixed
Nash distribution below is the product of the two free players' independent
Bernoulli actions.

For the singleton-base handoff, `d` Quits surely at date zero.  If `d`
deviates to Continue, a nonempty action set of `{x,y}` absorbs immediately;
only their joint-Continue cell reaches an accuracy-dependent near-minmax
punishment tail for `d`.  This is why the exact punishment value `chi_d`, not
an attained exact punishment strategy, appears in (13).  The checked
singleton-base compiler implements such tails at every requested accuracy
and controls arbitrary behavioral deviations.

## Source correspondence

The source declarations are:

- `two_le_card_freePlayers` and
  `disjoint_persistentBase_freePlayers` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleCycleFaces.lean`;
- `HasQuittingStrictToggleSemanticResidual` and
  `hasQuittingStrictToggleSemanticDispatch_of_card_four` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleSemanticDispatch.lean`;
- `quittingPersistentBaseNashSet`, the induced finite game, and compact Nash
  existence in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `quittingPersistentLargeBaseExcess` and
  `exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `quittingSingletonBaseOwnerFloorExcess`,
  `nonempty_quittingSingletonBaseCertificate_of_inducedNash`, and
  `exists_uniformPayoff_or_singletonBase_pos_gap` in that same file;
- `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
- `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`; and
- the finite but non-eliminated `3^|F|` support-status cover in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SupportStatusCells.lean`.

Those declarations supply the actual cycle faces, induced Nash carrier,
large-base `G`, positive compact gap, and all-behavior consumer.  They do not
state the two-by-two classification below or the cleared numerator (7).  The
new content is the exact elimination of the Nash-set quantifier in the only
four-player large-base cardinality, including all zero/equality faces and the
division-free paid-leave formula.  Also new is the same-rate base-deletion
test (11)--(15), which turns the large-base paid leave into the outsider field
of the checked singleton-base certificate.

No paper theorem is used.

## Proof

The disjoint sets `B` and `F` each contain at least two elements and lie in a
four-element set.  Hence both have cardinality two and their union is `I`.
There are no outside-player join components in `G`.

If the induced game has a pure Nash cell `(i,j)`, apply (2) to its point-mass
product distribution.  The free-player components of `G` are zero, so some
`c in B` has `ell_c^ij>=gamma`.  Conditions (5) are exactly the two pure
best-response inequalities.  This proves the first alternative.

Now suppose there is no pure Nash cell.  First, none of the four differences
in (3) is zero.  For example, if `alpha_0=0`, then:

- `beta_0<=0` makes `(0,0)` a pure Nash cell;
- if `beta_0>0` and `alpha_1<=0`, `(0,1)` is a pure Nash cell;
- if also `alpha_1>0` and `beta_1<=0`, `(1,0)` is a pure Nash cell; and
- if instead `beta_1>=0`, `(1,1)` is a pure Nash cell.

This exhausts the possibilities.  The other three zero cases follow by
exchanging rows, columns, or players.

The two `alpha` values cannot have the same sign: then `x` has one strict
best action against both columns, and a pure best response of `y` to that row
forms a pure Nash cell.  Thus their signs are opposite.  If
`alpha_0>0>alpha_1`, avoiding a Nash cell first at `(1,0)` and then at `(0,1)`
forces `beta_1>0>beta_0`.  Reversing the `alpha` signs gives the reverse
`beta` signs.  These are exactly (6+) and (6-).

No Nash equilibrium can now have a pure coordinate.  If `x` were pure, `y`
could mix only if the corresponding nonzero `beta_i` vanished; otherwise `y`
is pure, producing a forbidden pure Nash cell.  The same argument applies
with the players exchanged.  Hence both mix, and their two indifference
equations have the unique solution (9).  In either orientation both
probabilities lie strictly between zero and one, `D>0`, and direct
substitution gives (10).

All four numerators are positive and their sum is `D`.  Therefore the
expected leave gain of base member `c` is exactly `N_c/D`.  Applying (2) to
the unique mixed equilibrium gives a `c in B` with
`N_c/D>=gamma`.  Multiplication by `D>0` proves (8).

The pure and no-pure cases are exhaustive and mutually exclusive, completing
the two-by-two classification.

For the base-deletion dispatch, divide `R_x` by the nonzero
`alpha_0-alpha_1`.  Using (9), the result is exactly

```text
(1-t)bar_alpha_0+t bar_alpha_1.
```

Similarly, `R_y/(beta_1-beta_0)` is
`(1-s)bar_beta_0+s bar_beta_1`.  Thus `R_x=R_y=0` says precisely that the same
strictly interior product mixture is an induced Nash equilibrium when the
persistent base is reduced from `{c,d}` to `{d}`.

At that new root, `c` is the only outsider.  Its Continue and immediate-join
payoffs are

```text
V_c^-=(1/D) sum_(i,j) W_ij r_(D_ij)(c),
V_c^+=(1/D) sum_(i,j) W_ij r_(C_ij)(c).
```

Equations (3), (7), and (12) give

```text
V_c^- - V_c^+ = N_c/D >= gamma.                     (16)
```

Hence `c` satisfies the singleton-base certificate's outsider no-join field
with a strict margin.

If the sure owner `d` Continues, the three nonempty action sets of `{x,y}`
absorb immediately at `{x}`, `{y}`, or `{x,y}`.  Their joint-Continue cell
reaches the punishment tail priced at `chi_d`.  Consequently `K_d/D` is
exactly the owner's Continue-minus-prescribed-payoff floor excess.  Since
`D>0`, `K_d<=0` is precisely the owner-floor balance.  The two induced Nash
equalities, (16), and this floor balance satisfy
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  The checked
singleton-base consumer then supplies a uniform-equilibrium payoff against
all behavioral deviations.  A terminal exploitability witness excludes that
conclusion, proving (15).

## Boundary tests

For a strict pure example, take

```text
alpha_0=alpha_1=1,       beta_0=beta_1=1.
```

Both free players strictly prefer Quit, so `(1,1)` is the unique induced Nash
cell.  Setting `ell_a^11=2` gives (4) for every `0<gamma<=2`.  This tests that
dominance and boundary product distributions go to the pure branch rather
than being forced into the mixed formulas.

For the first matching-pennies orientation, take

```text
alpha_0=2, alpha_1=-1, beta_0=-3, beta_1=1.
```

Then `D=12`, the four cleared weights are `(1,3,2,6)`, and the mixed rates are
`s=3/4`, `t=2/3`.  If all four `ell_a^ij=1`, then `N_a=12`, so (8) holds with
`gamma=1`.  Reversing every sign,

```text
alpha_0=-2, alpha_1=1, beta_0=3, beta_1=-1,
```

tests the second orientation and gives the same positive cleared weights.

Zero differences cannot leak into the strict mixed branch.  The four-case
argument in the proof shows, for example, that `alpha_0=0` always creates a
pure Nash cell, including at equality `beta_i=0`.  This is the necessary
boundary test missing from a generic-position-only matching-pennies argument.

Finally, if every `ell_c^ij=0`, then `N_c=0` for both base members.  The
positive-gap hypothesis fails, as it must.  Thus the theorem does not create
a paid certificate from the two-by-two sign pattern alone.

The first mixed example also tests the singleton-base handoff.  Set

```text
bar_alpha_j=alpha_j,       bar_beta_i=beta_i,
all d-coordinate terminal rewards=0, hence chi_d=0,
r_R(d)=0                    for every nonempty R subset {x,y},
r_({d} union R)(d)=0        for every R subset {x,y}.
```

Then `R_x=R_y=K_d=0`.  Choose player `c`'s rows so that every
`ell_c^ij=1`.  The new root has the same mixed free-player equilibrium,
`c`'s outsider no-join margin is exactly one, and the owner floor is balanced;
the singleton-base compiler applies.

This handoff is not automatic.  Starting from the same mixed example, change
only `bar_alpha_0` by a nonzero amount while leaving `bar_alpha_1` fixed.
Then `R_x` changes by `-alpha_1` times that amount and is nonzero.  Likewise,
raising only `chi_d` makes `K_d>0` once the increase crosses the displayed
floor slack.  These exact perturbations test the two distinct residual types
in (15): failure to preserve the mixed free-player root and failure of the
punishment-priced owner balance.

## Adapter and consumer

The actual-data adapter is the checked strict-toggle semantic dispatch.  From
a four-player terminal exploitability witness and a reachable strict-toggle
cycle, `hasQuittingStrictToggleSemanticDispatch_of_card_four` returns either
an actual uniform payoff or one of three semantic residuals.  After excluding
the uniform-payoff branch, its large-base arm supplies `B`, `F`, `gamma>0`,
and exactly hypothesis (2).  The cardinal facts cited above supply (1).

This packet replaces that arm by the finite outputs (4) or (6)--(8).  The pure
output has no downstream semantic consumer yet.  In the mixed output,
(11)--(14) reach the checked constructor
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`, followed by
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff`.  If a terminal
witness rules out that consumer, (15) is the exact remaining residual.

If instead an original large-base Nash point had all base-leave excesses
nonpositive, the existing checked declaration
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` would be the
all-behavior consumer; hypothesis (2) excludes exactly that case.

## Lean handoff

The narrow reusable algebraic lemma should be stated first for a two-player
binary finite game.  Define:

- the four endpoint differences `alpha`, `beta`;
- a predicate for a pure Nash Boolean pair using (5);
- the two strict matching-pennies orientations;
- the cleared denominator `D`, weights from (10), and a supplied four-cell
  observable `ell`.

Prove a theorem of the form

```text
(forall p in binaryGameNashSet, gamma <= expectedObservableMax p)
  -> PurePaidCell gamma ell
     or MixedPaidCell gamma alpha beta ell.
```

The proof should split on the finite existence of a pure Nash cell.  In the
no-pure branch, prove the zero-difference exclusion before dividing, derive
the two sign orientations, construct the unique mixed point, and clear the
strictly positive `D` only at the final step.

Then specialize with `ell c i j` equal to (3), using
`quittingPersistentLargeBaseExcess` and the card-four face lemmas.  A
conjecture-facing wrapper may consume the large-base branch of
`HasQuittingStrictToggleSemanticResidual`; it must not package either finite
output as a uniform-payoff certificate.

For the mixed output, define the base-deleted differences, `R_x,R_y`, the
cleared weights, and `K_d`.  Prove directly that `R_x=R_y=0` places the point
in `quittingPersistentBaseNashSet reward {d} {x,y}`, that (8) gives the
outsider endpoint inequality for `c`, and that `K_d<=0` rewrites to
`quittingSingletonBaseOwnerFloorExcess<=0`.  Then invoke
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  The wrapper under
a terminal witness should return the disjunction (15), not assume it as a
structure field.

Useful finite tests are all `2^4` weak sign assignments for
`alpha_0,alpha_1,beta_0,beta_1`, plus the two exact numerical examples above.
No new infinite-profile or measure-theoretic machinery is required.

## Scope and nonclaims

This result does not prove a uniform-equilibrium payoff for every large-base
source or construct a quitting chronology.  It consumes the mixed subchamber
(14), but not the pure paid-leave output or any residual in (15).  It does not
solve the general singleton-base `G` residual, the empty-base `W` residual,
support three, or full support.  It does not assert that a particular pure or
mixed chamber is inhabited by every four-player game.

It does not replace the all-behavior semantic dispatch with a stationary
completeness theorem.  The only strategy object used in the new proof is a
one-stage product Nash equilibrium of a two-player binary induced game.  The
unrestricted-behavior statement remains solely in the named checked adapter
and consumer surrounding this finite residual.
