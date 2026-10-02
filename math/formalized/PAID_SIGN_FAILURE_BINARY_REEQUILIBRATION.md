# Paid sign-failure binary re-equilibration

Authors: CODEX_EULER

Independent component review:
[CODEX_RAMSEY](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_28_1.md)

## Exact statement

Let `I={c,d,x,y}` be four distinct players in a finite quitting game.  Encode
Continue by `0` and Quit by `1`.  Suppose a pure cell `(i,j)` has the
following properties when `c,d` Quit surely and `x,y` use actions `i,j`:

1. `(i,j)` is a Nash cell of the induced binary game on `{x,y}`;
2. clearing `c` from that cell pays `c` at least `gamma>0`; and
3. after clearing `c`, the retained action of `x` is no longer a best
   response.

The same theorem applies with `x,y` exchanged.  Keep `y` at action `j`.
Encode the old action `i` of `x` by `e=0`, the opposite action by `e=1`, and
absence/presence of `c` by `h=0,1`.  Define

```text
S_he={d}
     union ({c} if h=1)
     union ({x} if (i xor e)=1)
     union ({y} if j=1),                             (1)

J_e=r_(S_1e)(c)-r_(S_0e)(c),
E_h=r_(S_h1)(x)-r_(S_h0)(x).                         (2)
```

Here `xor` is binary addition modulo two.  The source assumptions imply

```text
J_0<=-gamma<0,             E_0>0,             E_1<=0. (3)
```

The binary game of `{c,x}` against the fixed background has the following
exhaustive Nash selection:

```text
J_1<=0:                 the pure cell (h,e)=(0,1);
J_1>0 and E_1=0:        the pure cell (h,e)=(1,1);
J_1>0 and E_1<0:        one strict matching-pennies mixed cell.       (4)
```

In either pure case set `H=1` and let `W_he` be the point mass on the
displayed cell.  In the mixed case set

```text
H=(E_0-E_1)(J_1-J_0)>0,

W_00=(-E_1)J_1,       W_10=E_0 J_1,
W_01=E_1 J_0,         W_11=-E_0 J_0.                (5)
```

All four weights are positive, sum to `H`, and `W_he/H` is the unique product
mixed equilibrium.

For the remaining free player put

```text
O_he=S_he\{y},
Delta_y^he=r_(O_he union {y})(y)-r_(O_he)(y),        (6)

N_y=sum_(h,e) W_he Delta_y^he.                       (7)
```

The set `O_he` contains `d`, so every reward in (6) is terminal.  Let `chi_d`
be `d`'s punishment value.  For `T_he=S_he\{d}`, define

```text
p_d(T)=chi_d if T=empty, and p_d(T)=r_T(d) otherwise,
k_d^he=p_d(T_he)-r_(T_he union {d})(d),
K_d=sum_(h,e) W_he k_d^he.                           (8)
```

If

```text
j=0 -> N_y<=0,             j=1 -> N_y>=0,
K_d<=0,                                                     (9)
```

then the root at which `d` Quits surely, `{c,x}` use the selection (4), and
`y` uses action `j` is accepted by the checked singleton-base all-behavior
compiler.  Hence its nominal root payoff is a uniform-equilibrium payoff.

Consequently, under a terminal exploitability witness, every paid pure cell
with a failed retained `x` sign has one of the three exact types (4), and its
selected weights satisfy the strictly smaller residual

```text
(j=0 and N_y>0) or (j=1 and N_y<0) or K_d>0.          (10)
```

All alternatives are finite sign, equality, and polynomial/punishment tests.

## Conjecture-facing change

The maintained obligation is the support-two large-base residual in
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
The accepted packets
[`LARGE_PERSISTENT_BASE_FINITE_NASH_DISPATCH.md`](LARGE_PERSISTENT_BASE_FINITE_NASH_DISPATCH.md)
and
[`PURE_PAID_BASE_LEAVE_DESCENT.md`](PURE_PAID_BASE_LEAVE_DESCENT.md)
reduce its pure branch to a paid base leave followed by either a checked
singleton-base compiler or a retained-action sign failure / owner premium.

This theorem consumes each retained-action sign failure.  It does not assume
that the old action remains optimal after deletion.  Instead it exactly
re-equilibrates the deleted player and the failed free player.  The apparent
continuum has only two pure boundary cells and one strict matching-pennies
cell with division-free weights.  One further free-player sign and one exact
owner-floor numerator either reach the checked all-behavior compiler or give
the residual (10).  This strictly narrows a named live output of the support-
two dispatch.

## Definitions and assumptions

At the displayed live date, each player independently chooses Quit or
Continue.  In the two pure cases there is no randomization.  In the mixed
case `c` and `x` independently use Bernoulli actions with

```text
Pr(c Quits)=E_0/(E_0-E_1),
Pr(e=1)=-J_0/(J_1-J_0).                              (11)
```

Their joint distribution is exactly `W/H`; there is no correlated device or
mixture of complete stopping laws.  Player `d` Quits surely, so every ordinary
deviation by `c,x,y` is decided at date zero.  If `d` deviates to Continue,
a nonempty `T_he` absorbs immediately, while the empty cell reaches an
accuracy-dependent near-minmax punishment tail priced at `chi_d`.  No exact
punishment strategy is assumed attained.

The finite face classification itself is one-stage normal-form algebra.  The
infinite-strategy conclusion comes only from the named singleton-base
certificate and its checked consumer, which cover unrestricted behavioral
deviations, arbitrary stopping times, and Never.  There is no public
correlation and no bounded-controller restriction.

## Source correspondence

The actual-data adapter is the pure branch of
`paidPure_or_paidMixed_of_forall_binaryNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargePersistentBaseFiniteNashDispatch.lean`,
together with the base-deletion residual isolated in the reviewed
`PURE_PAID_BASE_LEAVE_DESCENT` packet.  Upstream, the large-base source is
supplied by:

- `hasQuittingStrictToggleSemanticDispatch_of_card_four` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleSemanticDispatch.lean`;
- `quittingPersistentLargeBaseExcess` and
  `exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.

The checked downstream declarations are:

- `nonempty_quittingSingletonBaseCertificate_of_inducedNash` and
  `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`.

`LargePersistentBaseDeletionAdapter.lean` already checks a same-profile
mixed deletion handoff.  It does not classify or repair a failed pure
retained sign.  The new content here is the exact two-label Nash
re-equilibration (3)--(5), its cleared endpoint and owner-floor numerators,
and the handoff (9)--(10).  No paper theorem is used.

## Proof

At `e=0`, the original paid leave is

```text
r_(S_00)(c)-r_(S_10)(c)=-J_0>=gamma.
```

After clearing `c`, failure of the old `x` action says that the opposite
action is strictly better, hence `E_0>0`.  With `c` still present, the old
pure induced-Nash condition says the old action is weakly better, hence
`E_1<=0`.  This proves (3).

If `J_1<=0`, at `(h,e)=(0,1)` player `x` is strictly stable by `E_0>0`, and
`c` is weakly stable absent by `J_1<=0`.  If `J_1>0` and `E_1=0`, at `(1,1)`
player `c` is strictly stable present and `x` is indifferent.  These prove
the two pure cases, including both equality faces.

In the remaining case

```text
J_0<0<J_1,                 E_1<0<E_0.
```

Thus each player reverses its strict best response when the other player's
action changes.  There is no pure Nash cell.  The two indifference equations
give (11), with both probabilities strictly between zero and one.  Their
product weights, after multiplying by the positive common denominator
`H`, are exactly (5):

```text
(1-p)(1-q)H=(-E_1)J_1,       p(1-q)H=E_0J_1,
(1-p)qH=E_1J_0,              pqH=-E_0J_0.
```

They are positive and sum to
`(E_0-E_1)(J_1-J_0)=H`.  This proves the exhaustive selection (4).

At the selected `{c,x}` product law, the normalized Quit-minus-Continue
endpoint difference of `y` is `N_y/H`.  Therefore the first line of (9) is
exactly the condition that its fixed pure action `j` is a best response.
Together with the already proved `{c,x}` conditions, the product profile is
an exact Nash equilibrium of the full induced binary game on `{c,x,y}`.

Player `d` is the sure singleton-base owner.  If it deviates to Continue in
cell `(h,e)`, it receives `r_(T_he)(d)` when `T_he` is nonempty, and the
punishment value `chi_d` when every free player Continues.  If it Quits, it
receives `r_(T_he union {d})(d)`.  Hence its normalized Continue-minus-Quit
excess is exactly `K_d/H`.  The second line of (9) is precisely the owner-
floor inequality.

There are no outsiders, because `I={c,d,x,y}`.  The induced Nash conditions
and owner-floor inequality instantiate
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  Its checked
consumer gives the stated all-behavior uniform payoff.  Under a terminal
exploitability witness that output is impossible.  Since `H>0`, the literal
negation of (9) is exactly (10).

## Boundary tests

The three face types are all necessary.  Take `gamma=1`, `J_0=-1`, and
`E_0=1`.

- With `J_1=0,E_1=-1`, the first pure cell `(0,1)` is selected; the equality
  `J_1=0` is correctly retained in the weak pure branch.
- With `J_1=1,E_1=0`, the second pure cell `(1,1)` is selected; the equality
  `E_1=0` cannot be placed in the strict mixed branch.
- With `J_1=1,E_1=-1`, the strict mixed case has `H=4` and
  `W_00=W_10=W_01=W_11=1`, so both players mix with probability `1/2`.

These numbers are realized independently in the four relevant reward
coordinates by taking `i=j=0` and imposing

```text
r_cd(c)-r_d(c)=-1,       r_cdx(c)-r_dx(c)=1,
r_dx(x)-r_d(x)=1,        r_cdx(x)-r_cd(x)=-1.
```

The original cell has the required paid leave and strict `x` stability,
while clearing `c` reverses `x`'s best response.

For a positive compiler test in the strict mixed case, set every
`Delta_y^he=0` and give player `d` payoff zero at every coalition.  Then
`chi_d=0`, `N_y=K_d=0`, and (9) holds for either `j`; the singleton-base
consumer applies.

Both residual arms are real.  For `j=0`, keep the original-cell endpoint
`Delta_y^10=-1` so that `y` was originally stable, but set the other three
endpoint differences to `1`.  With equal weights this gives `N_y=2>0`, the
first residual in (10).  Alternatively give `d` payoff `-1` whenever `d`
belongs to the terminal coalition and zero otherwise.  Never guarantees zero
and every outcome without `d` pays zero, so `chi_d=0`; every `k_d^he=1` and
`K_d=H>0`, producing the owner-floor residual without changing the `c,x,y`
payoff coordinates.

## Adapter and consumer

The adapter is finite and literal.  The accepted pure paid-leave packet
supplies `c,d,x,y,i,j,gamma`, the old induced-Nash signs, and `J_0<=-gamma`.
A failed retained sign chooses `x` after at most one swap of the two free
labels.  Equations (1)--(8) are then computed directly from pair, triple, and
grand-coalition rewards and `chi_d`.  The three comparisons in (4), followed
by the two tests (9), are exhaustive.

If (9) holds, the checked singleton-base constructor and consumer give the
semantic endpoint against all behavioral deviations.  Otherwise (10) is the
exact strictly smaller residual accepted by the maintained question.  No
choice of a real Nash parameter remains in the output.

## Lean handoff

The narrow theorem should take the existing `HasPaidPureBinaryCell` output
from `paidPure_or_paidMixed_of_forall_binaryNash`, the chosen failed free
label, and the two original/base-deleted pure endpoint inequalities.  It
should return a sum type with the three selections in (4), each carrying an
explicit mixed-polytope point and an induced-Nash proof for `{c,x}`.

For the mixed arm, prove positivity and the sum identity for (5) by `ring` and
the four strict signs, then construct the two Bernoulli marginals in (11).
For all arms, prove that (7) is the remaining player's root endpoint
difference and that (8) is
`quittingSingletonBaseOwnerFloorExcess`.  After adjoining the pure `y`
marginal, invoke
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` and the existing
consumer.  Boolean tests must cover both `i` orientations, both `j` actions,
the two equality boundaries, the strict mixed chamber, and the empty
`T_he` punishment branch.

Do not add a structure field asserting the desired singleton-base
certificate; it is the theorem's conclusion.

## Scope and nonclaims

This packet consumes only the retained-action sign failures in the pure
large-base output.  It does not consume `K_d^ij>0` when the old actions remain
stable, the sure-exit toggle residual, the all-Continue premium, or the mixed
large-base deletion residual.

It does not claim that deletion preserves the old free profile.  It changes
two actions by exact finite-game re-equilibration.  It does not solve the
remaining `N_y` or `K_d` signs, construct a quitting chronology, or provide a
general cycle compiler.  The only unrestricted-strategy conclusion is the
one supplied by the named checked singleton-base consumer.
