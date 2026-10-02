# Pure paid base-leave descent

Authors: CODEX_EULER

Independent review:
[CODEX_RAMSEY](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_27.md)

## Exact statement

Let `I={c,d,x,y}` be four distinct players in a finite quitting game.  Put
`B={c,d}` and `F={x,y}`.  Encode the two free players' pure actions by
`i,j in {0,1}`, with `0=Continue` and `1=Quit`, and define

```text
R_ij=({x} if i=1) union ({y} if j=1),
C_ij={c,d} union R_ij,
D_ij={d} union R_ij.                                  (1)
```

Assume `(i,j)` is a pure Nash cell of the induced binary game in which both
members of `B` Quit surely, and assume that `c` has a paid base leave of size
`gamma>0`:

```text
r_(D_ij)(c)-r_(C_ij)(c) >= gamma.                    (2)
```

For the square after deleting `c`, define

```text
D_kl={d} union ({x} if k=1) union ({y} if l=1),

bar_alpha_l=r_(D_1l)(x)-r_(D_0l)(x),
bar_beta_k =r_(D_k1)(y)-r_(D_k0)(y).                (3)
```

The retained actions are base-deleted stable when

```text
i=0 -> bar_alpha_j<=0,       i=1 -> bar_alpha_j>=0,
j=0 -> bar_beta_i <=0,       j=1 -> bar_beta_i >=0. (4)
```

Let `chi_d` be player `d`'s punishment value, and put

```text
K_d^ij =
  if R_ij=empty then chi_d-r_{d}(d)
  else r_(R_ij)(d)-r_(D_ij)(d).                     (5)
```

Then the following statements hold.

### Singleton-base descent

If (4) holds and `K_d^ij<=0`, the root at which `d` Quits surely, `x,y` play
the pure actions `(i,j)`, and `c` Continues is accepted by the checked
singleton-base all-behavior compiler.  Its fixed nominal date-zero payoff is
a uniform-equilibrium payoff.

Consequently, under a terminal exploitability witness, every such pure paid
cell satisfies the exact finite residual

```text
(i=0 and bar_alpha_j>0) or (i=1 and bar_alpha_j<0)
or
(j=0 and bar_beta_i>0) or (j=1 and bar_beta_i<0)
or
K_d^ij>0.                                             (6)
```

### Sure-exit descent

Extend the reward notation to the empty set by `hat_r_empty=0` and
`hat_r_S=r_S` for nonempty `S`.  Suppose `R_ij` is nonempty and `K_d^ij>0`.
If

```text
hat_r_(R_ij\{z})(z) <= r_(R_ij)(z)       for every z in R_ij,
r_(R_ij union {z})(z) <= r_(R_ij)(z)     for every z in F\R_ij,
r_(R_ij union {c})(c) <= r_(R_ij)(c),                (7)
```

then `R_ij` is an exact sure-exit set and `r_(R_ij)` is a
uniform-equilibrium payoff against unrestricted behavioral deviations.

Consequently, under a terminal exploitability witness, every nonempty
positive-premium cell satisfies

```text
exists z in R_ij,
  hat_r_(R_ij\{z})(z)>r_(R_ij)(z),
or exists z in F\R_ij,
  r_(R_ij union {z})(z)>r_(R_ij)(z),
or r_(R_ij union {c})(c)>r_(R_ij)(c).                (8)
```

## Conjecture-facing change

The maintained obligation is the large-persistent-base `G` arm in
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
The accepted packet
[`LARGE_PERSISTENT_BASE_FINITE_NASH_DISPATCH.md`](LARGE_PERSISTENT_BASE_FINITE_NASH_DISPATCH.md)
eliminates its induced-Nash quantifier.  Its pure output is exactly the source
assumed here: an internally stable induced-game vertex with one
`gamma`-paid base leave.

This packet strictly narrows that pure output twice.  Deleting the paid base
member either reaches the checked singleton-base compiler or leaves two
strict base-deleted best-response failures and one punishment premium (6).
If the premium is positive at a nonempty retained action set, deleting the
remaining base member either reaches the checked sure-exit compiler or leaves
one of the three explicit membership-toggle failures (8).  The
all-Continue cell remains separately and exactly identified by
`K_d^00=chi_d-r_d(d)`.

## Definitions and assumptions

At a live date, the pure roots in this packet use no randomization: each
player either Quits surely or Continues surely.  A nonempty first-quitter
coalition absorbs immediately.  The induced Nash assumption at `C_ij` means
that neither `x` nor `y` profits by toggling its date-zero membership while
both base members Quit.

After deleting `c`, player `d` still Quits surely.  Thus a unilateral
deviation by `x`, `y`, or outsider `c` is decided by its date-zero membership
choice.  If `d` deviates to Continue and `R_ij` is nonempty, absorption occurs
at `R_ij`; if `R_ij` is empty, the continuation is priced at the exact
punishment value `chi_d` and implemented by accuracy-dependent near-minmax
punishment rows.  No exact punishment strategy is assumed attained.

After deleting `d` as well, the second theorem uses the pure stationary
sure-exit root for the nonempty set `R_ij`.  The checked sure-exit theorem
computes every unrestricted behavioral deviator's cap as the better of its
two membership toggles, including arbitrary stopping times and Never.

There is no public correlation, stopping-law mixture, or restriction to a
bounded controller.

## Source correspondence

The actual-data source is the pure arm of the independently reviewed packet
`LARGE_PERSISTENT_BASE_FINITE_NASH_DISPATCH`.  Upstream, its data come from:

- `hasQuittingStrictToggleSemanticDispatch_of_card_four` and
  `hasQuittingStrictToggleSemanticResidual_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleSemanticDispatch.lean`;
- `quittingPersistentLargeBaseExcess` and
  `exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.

The checked consumers used here are:

- `nonempty_quittingSingletonBaseCertificate_of_inducedNash` and
  `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`;
- `IsQuittingSureExitSet`,
  `isQuittingSureExitSet_iff_forall_max`, and
  `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

The new content is the exact source-to-consumer translation: a paid base
leave becomes the deleted player's strict outsider no-join field, while the
remaining player's leave becomes the next deleted player's no-join field.
The empty/nonempty distinction in (5) records exactly when a punishment tail
is needed.

No paper theorem is used.

## Proof

Conditions (4) say exactly that the pure point `(i,j)` is an induced Nash
equilibrium of the free binary game with persistent base `{d}`.  At this new
root, `c` is the only outsider.  Its Continue payoff is `r_(D_ij)(c)`, while
joining gives `r_(C_ij)(c)`.  By (2), the outsider no-join inequality holds
with margin at least `gamma`.

It remains to check the sure owner `d`.  If `R_ij` is nonempty, at least one
of `x,y` Quits surely.  If `d` Continues, date-zero absorption is therefore at
`R_ij`, whereas Quit gives the nominal coalition `D_ij`; its owner-floor
Continue-minus-Quit excess is the second line of (5).  If `R_ij` is empty,
every other player Continues, so the Continue endpoint is the punishment
value `chi_d`, while Quit pays the solo reward `r_d(d)`; the excess is the
first line of (5).

Thus (4), (2), and `K_d^ij<=0` are precisely the induced Nash, outsider, and
owner-floor hypotheses of
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  Its checked
consumer proves the first positive conclusion.  Under a terminal witness
that conclusion is impossible, and the literal negation of the weak
inequalities is (6).

Now assume `R_ij` is nonempty and `K_d^ij>0`.  The second line of (5) gives

```text
r_(R_ij)(d)>r_({d} union R_ij)(d).                  (9)
```

After deleting `d`, this is its strict outsider no-join inequality at the
exit set `R_ij`.  The first line of (7) is the no-leave inequality for every
member of that set.  It remains meaningful when `R_ij` is a singleton because
the payoff after its sole member leaves is the Never payoff zero.  The second
line controls every other free player, the third controls `c`, and (9)
controls `d`.  These labels exhaust `I`.

Hence (7) and (9) are exactly all membership-toggle inequalities in
`IsQuittingSureExitSet reward R_ij`.  The checked sure-exit consumer proves
the second positive conclusion.  A terminal witness excludes it, and the
finite negation of (7) is (8).

## Boundary tests

The empty retained cell is essential.  If `i=j=0`, then `R_00=empty` and

```text
K_d^00=chi_d-r_d(d).
```

When this is nonpositive and the two base-deleted Continue signs in (4) hold,
the singleton-base compiler applies using a punishment tail.  When it is
positive, there is no nonempty sure-exit set to which the second theorem can
descend; the packet explicitly leaves that premium unresolved.

For a nonempty exact test, take `i=1,j=0`, so `R={x}`.  Set

```text
gamma=1,
r_({d,x})(c)=1,              r_({c,d,x})(c)=0,
bar_alpha_0=1,               bar_beta_1=-1,
r_x(d)=1,                    r_({d,x})(d)=0.
```

Then the paid leave is one, the retained actions remain strict best
responses, and `K_d^10=1>0`.  Complete the relevant sure-exit coordinates by

```text
r_x(x)=1,
r_({x,y})(y)=r_x(y)=0,
r_({c,x})(c)=r_x(c)=0.
```

The member `x` does not leave, outsiders `y,c` do not join, and (9) strictly
controls `d`; `{x}` is a sure-exit set and its checked compiler applies.
All unspecified payoff coordinates can be chosen independently, so these
equalities are consistent with an original pure induced Nash cell by taking
its original differences, for example, to be `alpha_0=1` and `beta_1=-1`.

For the singleton-base rather than sure-exit branch, keep the same paid leave
and retained signs but set `r_x(d)=0`, `r_({d,x})(d)=1`.  Then
`K_d^10=-1`, so the first compiler applies directly.

Finally, changing only `bar_alpha_0` from `1` to `-1` produces the first
strict reprojection failure in (6) without altering the original pure-cell
data.  This verifies that deleting a base member does not automatically
preserve the free-player best response.

## Adapter and consumer

The adapter is finite and literal.  The accepted large-base packet supplies
`B,F,i,j,c,gamma` and (2).  Taking `d` as the other base member defines every
quantity in (1)--(5) directly from the reward table and punishment value.

If (4) and `K_d^ij<=0` hold, the checked singleton-base certificate constructor
and consumer give a fixed nominal uniform payoff against all behavioral
deviations.  If instead `R_ij` is nonempty, `K_d^ij>0`, and (7) holds, the
checked sure-exit constructor and consumer give the payoff `r_(R_ij)`.
Otherwise (6) or (8) is the exact strictly smaller residual accepted by the
maintained question.

## Lean handoff

Define a pure large-base paid-leave certificate carrying two base labels, two
free labels, Boolean actions, the original pure induced Nash proof, and the
paid inequality (2).  Do not store either desired compiler conclusion.

For the first theorem:

1. build the pure mixed-polytope point on free set `{x,y}`;
2. rewrite its induced Nash conditions to (4);
3. rewrite (2) to the outsider endpoint inequality after deleting `c`;
4. prove by cases on `R_ij.Nonempty` that (5) is exactly
   `quittingSingletonBaseOwnerFloorExcess`; and
5. invoke `nonempty_quittingSingletonBaseCertificate_of_inducedNash` and its
   checked consumer.

For the second theorem, use `quittingSetReward` to avoid a separate empty-set
reward definition.  Rewrite `K_d^ij>0` to (9), assemble
`IsQuittingSureExitSet reward R_ij` from (7), (9), and the four-label
exhaustion, then invoke
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`.

Finite tests should cover all four Boolean cells.  In particular, test the
empty cell separately from the three nonempty cells and check both singleton
member erasures against `quittingSetReward reward empty=0`.

## Scope and nonclaims

This packet does not consume the strict residuals (6) or (8), nor the empty
premium `chi_d>r_d(d)`.  It does not address the mixed matching-pennies
residual, which is handled separately in the accepted large-base packet.  It
does not prove that deleting a base member preserves any best response; it
tests that fact exactly.

No new cycle geometry, stationary-support completeness, or quitting
chronology is claimed.  The only infinite-strategy conclusions are supplied
by the named checked singleton-base and sure-exit consumers.
