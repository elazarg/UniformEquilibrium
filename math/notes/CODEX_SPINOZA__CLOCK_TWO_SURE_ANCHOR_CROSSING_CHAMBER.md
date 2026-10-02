# A clock-two sure-anchor crossing chamber

**Author:** CODEX_SPINOZA  
**Status (2026-09-03):** reusable theorem and exact toggle-boundary dispatch
proved in ordinary mathematics; not Lean-checked and not reviewed.  It
extracts the structural open chamber containing the exact E2 profile without
altering the frozen E2 certificate.  The toggle analysis is sharp: two
semialgebraic residuals admit square-free exact regressions, and an anchor
failure can be carried by a pure opponent externality rather than a new
membership toggle.

## 1. Question and data

Let `a,b,c,d` be four distinct players.  Write `R_i(S)` for player `i`'s
terminal reward when the nonempty quitting coalition is `S`.  We seek an exact
terminal Nash profile of the following clock-two form:

```text
date 0:  a quits with probability x,
         b quits surely,
         c quits with probability y,
         d continues;

date 1, conditional on survival:
         the surviving a and c quit surely,
         d continues;

after date 1:
         d never quits.
```

Thus the vector of date-zero quitting probabilities is `(x,1,y,0)` in the
ordered coordinates `(a,b,c,d)`.  The choices are independent.  The target is
an unrestricted behavioral terminal Nash profile, not merely a Nash point of
the three-action menu.

## 2. Crossing contrasts and the unique active probabilities

Define four reward contrasts:

```text
L_a = R_a({b})     - R_a({a,b}),
G_a = R_a({a,b,c}) - R_a({b,c}),

G_c = R_c({b,c})   - R_c({b}),
L_c = R_c({a,b})   - R_c({a,b,c}).
```

Assume

```text
L_a > 0,   G_a > 0,   G_c > 0,   L_c > 0.                 (2.1)
```

Player `a`'s advantage from joining the date-zero coalition rather than
waiting is

```text
-(1-y)L_a + y G_a.
```

Player `c`'s analogous advantage is

```text
(1-x)G_c - x L_c.
```

Consequently the two active indifference equations have the unique interior
solution

```text
x = G_c / (G_c + L_c),
y = L_a / (L_a + G_a).                                   (2.2)
```

For rational rewards these are rational probabilities.  Put

```text
A = L_a + G_a,        C = G_c + L_c
```

and introduce the positive unnormalized outcome weights

```text
w_00 = L_c G_a,       w_10 = G_c G_a,
w_01 = L_c L_a,       w_11 = G_c L_a.                    (2.3)
```

They sum to `AC`; divided by `AC`, they are the probabilities at date zero of
the coalitions `{b}`, `{a,b}`, `{b,c}`, and `{a,b,c}`, respectively.

For every player `i`, define the unnormalized on-path payoff

```text
U_i = w_00 R_i({b})
    + w_10 R_i({a,b})
    + w_01 R_i({b,c})
    + w_11 R_i({a,b,c}).                                 (2.4)
```

The actual on-path payoff is `u_i = U_i/(AC)`.

## 3. The three remaining finite inequalities

If the sure anchor `b` deviates to quitting at date 1, its unnormalized payoff
is

```text
V_b^1 = w_00 R_b({a,b,c})
      + w_10 R_b({a})
      + w_01 R_b({c})
      + w_11 R_b({a,c}).                                 (3.1)
```

If `b` quits strictly after date 1 or Never, its unnormalized payoff is

```text
V_b^late = w_00 R_b({a,c})
         + w_10 R_b({a})
         + w_01 R_b({c})
         + w_11 R_b({a,c}).                              (3.2)
```

Finally, if the passive player `d` joins at date zero, its unnormalized payoff
is

```text
V_d^0 = w_00 R_d({b,d})
      + w_10 R_d({a,b,d})
      + w_01 R_d({b,c,d})
      + w_11 R_d({a,b,c,d}).                             (3.3)
```

The finite rational chamber criterion is

```text
U_b >= V_b^1,        U_b >= V_b^late,        U_d >= V_d^0.    (3.4)
```

Together, (2.1) and (3.4) are seven scalar comparisons.  No division occurs
in (3.4), and every coefficient is a polynomial in the four contrasts.

## 4. Exact chamber theorem

### Theorem 4.1 (sure-anchor crossing profile)

Suppose (2.1) and (3.4) hold.  Define `x,y` by (2.2) and use the clock-two
profile of Section 1.  Then the profile is exact terminal Nash against every
unilateral behavioral deviation.  Its payoff is `i |-> U_i/(AC)`, and that
vector is a uniform-equilibrium payoff.

#### Proof

Because `b` quits surely at date zero, a pure-time deviation by `a` has only
two payoff-distinct choices: join at date zero or wait.  Their difference is
`-(1-y)L_a+yG_a`, which is zero by (2.2).  The same argument for `c` gives
the difference `(1-x)G_c-xL_c=0`.  Therefore both actions in the support of
each mixer attain its on-path payoff, and no other pure time gives a different
value.

For `d`, waiting at least one date gives its on-path payoff because `b` has
already stopped the game.  Its only other pure-time value is quitting at date
zero, namely `V_d^0/(AC)`, and the third inequality in (3.4) rules it out.

For `b`, Q0 is the prescribed action and has value `U_b/(AC)`.  If `b` uses
Q1, then whenever neither mixer quit at date zero, both surviving mixers join
`b` at date one; exact enumeration gives (3.1).  If `b` waits longer, the two
surviving mixers quit without `b`, giving (3.2).  Every later finite time and
Never has that same second value.  The first two inequalities in (3.4) rule
out both deviation classes.

Thus every pure stopping time yields at most the on-path payoff.  The checked
behavioral pure-time extremality theorem
`quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` upgrades
these comparisons to arbitrary behavioral unilateral updates.  The profile
is exact terminal Nash.  The checked theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` supplies the
uniform-payoff conclusion.  QED.

## 5. Open chamber and arbitrary coordinates

If all three inequalities in (3.4) are strict, (2.1)--(3.4) define an open
semialgebraic chamber in the reward coordinates they use.  The chosen
probabilities vary continuously by (2.2), so this is a structural chamber,
not a fixed-probability knife edge.

Only 23 of the 60 player-by-coalition reward coordinates occur:

- four coordinates each for players `a` and `c`;
- seven coordinates for the anchor `b`; and
- eight coordinates for the passive player `d`.

The other 37 reward coordinates are arbitrary and unbounded.  Thus the
criterion is also an unbounded cylinder in the full space of Fin4 quitting
tables.

The active equations create exact ties for `a` and `c`: each is indifferent
between Q0 and waiting.  This tie does **not** permit arbitrary movement of
their residual mass.  Having both residual masses quit at the immediately
following date is what creates the anchor screens (3.1)--(3.2).  The passive
player's own action can, however, be replaced by any stopping law supported
strictly after date 1 (including Never), because every play relevant to a
unilateral deviation has already absorbed by then.

## 6. E2 lies strictly inside the chamber

Use `(a,b,c,d)=(0,1,2,3)`.  In E2,

```text
(L_a,G_a,G_c,L_c) = (3,8,1,1),
x = 1/2,        y = 3/11,
(w_00,w_10,w_01,w_11) = (8,8,3,3),
AC = 22.
```

The three strict screening margins in actual payoff scale are

```text
u_b - v_b^1    = 29/44,
u_b - v_b^late =  5/44,
u_d - v_d^0    =  3/11.
```

Hence E2 is not merely a boundary point of the criterion.  It lies in the
strict open chamber, with substantial rational slack in every inactive
deviation direction.

## 7. Scope and next question

The theorem is a supplied-data sufficient condition, not a producer from an
arbitrary Fin4 table.  It does not show that a hard residual can always be
relabelled into this chamber.  Its value is that it converts a recognizable
crossing pattern around one sure anchor into an exact unrestricted terminal
Nash profile while leaving most reward coordinates free.

**Next question.**  Is there a checked hard-residual dispatch whose endpoint
forces, after relabelling, the four crossing signs (2.1) and at least one of
the two anchor delay screens?  The passive screen is logically separate and
should not be inferred from the crossing equations.

## 8. Sources and declarations inspected

- `../UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`:
  `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime`.
- `../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`.
- `notes/CODEX_SPINOZA__E2_CLOCK_TWO_EXACT_TERMINAL_NASH.md`: the exact E2
  profile from which the chamber was extracted; that frozen note was not
  edited during this derivation.
- `notes/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`, Sections
  9--15: reachable strict-toggle cycles, the existing singleton-base
  matching-pennies compiler, and the exact persistent/empty-base
  semialgebraic residuals.
- `notes/CODEX_SNELL__PERSISTENT_BASE_SEMIALGEBRAIC_RESIDUAL.md`, Sections
  1--4 and 9--10: literal realization of persistent excess and the
  empty-base cleared stationary field.  The present note does not import its
  later source-attachment claims.

## 9. Relation to the checked singleton-base four-cycle

The four signs (2.1) orient the coalition square

```text
{b} -> {b,c} -> {a,b,c} -> {a,b} -> {b}.             (9.1)
```

Indeed the four edges are, in order, `c` joining, `a` joining, `c` leaving,
and `a` leaving.  Thus Theorem 4.1 is a new temporal consumer for exactly the
singleton-base matching-pennies cycle treated statically in Section 10 of
`CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.  The constructions
are different: the existing result prices the blocker's all-Continue event by
its punishment value, whereas this note makes the two surviving mixers quit
together at the next date and checks the blocker's two absolute deadline
classes directly.

A general reachable strict-toggle cycle need not contain (9.1).  Every
four-cycle is a two-dimensional face, but its persistent base can have size
zero, one, or two.  Longer cube cycles can be square-free.  Therefore this
consumer applies exactly to the singleton-base four-cycle branch, not to an
arbitrary selected cycle.

## 10. What each failed chamber inequality really supplies

Let the normalized weights `w_00,w_10,w_01,w_11` be as in (2.3).  Define the
four passive join gains

```text
j_d(S) = R_d(S union {d})-R_d(S)
          for S in {{b},{a,b},{b,c},{a,b,c}}.        (10.1)
```

Then

```text
V_d^0-U_d = sum_S w_S j_d(S).                        (10.2)
```

All weights are positive.  Hence failure of the passive screen produces one
literal strict outgoing join edge

```text
S -> S union {d},        j_d(S)>0,                   (10.3)
```

from a vertex of the original square.

The anchor screens have a different structure.  Put

```text
ell_a  = R_b({a})   - R_b({a,b}),
ell_c  = R_b({c})   - R_b({b,c}),
ell_ac = R_b({a,c}) - R_b({a,b,c}),

e_1    = R_b({a,b,c})-R_b({b}),
e_late = R_b({a,c})  -R_b({b}).                      (10.4)
```

Exact subtraction of (3.1)--(3.2) from (2.4) gives

```text
V_b^1-U_b =
  w_00 e_1+w_10 ell_a+w_01 ell_c+w_11 ell_ac,

V_b^late-U_b =
  w_00 e_late+w_10 ell_a+w_01 ell_c+w_11 ell_ac.     (10.5)
```

Consequently:

1. if the Q1 screen fails and `e_1<=0`, some `ell` is positive;
2. if the late screen fails and `e_late<=0`, some `ell` is positive; and
3. a positive `ell` is a literal strict base-leave edge from `{a,b}` to
   `{a}`, from `{b,c}` to `{c}`, or from `{a,b,c}` to `{a,c}`.

Thus an anchor failure produces a new outgoing toggle unless it is carried by
one of the two diagonal externalities

```text
R_b({a,b,c})>R_b({b})
or
R_b({a,c})>R_b({b}).                                 (10.6)
```

These compare outcomes differing in two or three membership coordinates.
They are payoff changes **observed by `b`**, not unilateral membership
toggles by either mixer.  No strict-toggle edge follows from (10.6) alone.

### Proposition 10.1 (finite failure dispatch)

For a supplied singleton-base strict four-cycle (9.1), exactly one of the
following tests returns:

```text
(i)   the three screens (3.4) pass, and Theorem 4.1 compiles;
(ii)  the passive screen fails, giving (10.3);
(iii) an anchor screen fails and gives a strict b-leave edge;
(iv)  an anchor screen fails with the corresponding positive diagonal
      externality in (10.6).                         (10.7)
```

The tests are finite rational comparisons.  Under a terminal exploitability
witness, the strict edge in (ii) or (iii) may be followed by the checked
outgoing-toggle construction until a simple cycle is reached.  That operation
does not retain the entering edge on the eventual cycle: it can lie in the
discarded preperiod.  Hence (ii)--(iii) give an anchored strict path, but not
by themselves a smaller compiler-accepted cycle.

## 11. Exact anchor-externality regression

The diagonal alternative (iv) cannot be deleted.  Retain the E2-sized
crossing contrasts

```text
(L_a,G_a,G_c,L_c)=(3,8,1,1),
```

so `(x,y)=(1/2,3/11)` and the unnormalized weights are `(8,8,3,3)`.
Give the anchor the rewards

```text
R_b(empty)=R_b({b})=0,
R_b({a})=R_b({a,b})=0,
R_b({c})=R_b({b,c})=0,
R_b({a,c})=R_b({a,b,c})=1.                          (11.1)
```

Then every own-membership comparison of `b` on the `{a,c}` subcube is a
tie.  In particular there is no strict `b`-toggle at all on these four edges.
Nevertheless

```text
U_b/(AC)       = 3/22,
V_b^1/(AC)     = 1/2,
V_b^late/(AC)  = 1/2.                               (11.2)
```

Both anchor screens fail by `4/11`.  The gain comes solely from the fact that
delaying allows the two opponents to arrive together.  It is not the gain
from adding or removing `b` at a fixed opponent coalition.

The passive screen can simultaneously be made strict in the safe direction:
pay `d` zero on the four square vertices and `-1` when it joins any of them.
All unused coordinates may be set to zero.  Thus even one exact
singleton-base four-cycle plus strict passive contentment does not convert an
anchor-screen failure into a new toggle.  A consumer of (11.1) needs an
observer-externality argument, not another coalition-graph traversal.

## 12. The residuals do not force a hidden square

There is also a direct exact regression against extracting (9.1) from either
cycle geometry or the empty-base semialgebraic residual.

On three active players `1,2,3`, orient only the six edges

```text
empty -> {1} -> {1,2} -> {1,2,3}
      -> {2,3} -> {3} -> empty.                     (12.1)
```

This is a square-free induced six-cycle.  It is realized by the following
playerwise rewards on the three-cube; empty reward is zero:

```text
player 1:
  R_1({1})=1,
  R_1({2})=R_1({1,2})=2,
  R_1({3})=R_1({1,3})=2,
  R_1({2,3})=2, R_1({1,2,3})=1;

player 2:
  R_2({2})=0,
  R_2({1})=0, R_2({1,2})=1,
  R_2({3})=1, R_2({2,3})=0,
  R_2({1,3})=R_2({1,2,3})=0;

player 3:
  R_3({3})=-1,
  R_3({1})=R_3({1,3})=0,
  R_3({2})=R_3({2,3})=0,
  R_3({1,2})=0, R_3({1,2,3})=1.                   (12.2)
```

Each player's two unused membership edges are ties, so (12.1) is the entire
strict-toggle graph on this face.  Add a fourth passive player and set every
coordinate on coalitions containing it to zero; this creates no further
strict edge.

Let `x,y` be the interior stationary Quit probabilities of players 2 and 3,
and put `d=x+y-xy`.  For player 1, the cleared stationary indifference
polynomial from the existing empty-base screen is exactly

```text
H_1(x,y) = -d ((1-x)(1-y)+xy) < 0                  (12.3)
```

throughout `(0,1)^2`.  Hence the empty-base system has no interior root,
independently of player 1's own rate and of the passive inequality.  This is
an exact instance of residual (15.3) in the Euler dispatch whose strict graph
contains no four-cycle at all.

The persistent-base residual admits the same obstruction.  Add a fourth
player `b`, duplicate (12.2) on both the `b`-absent and `b`-present faces for
players 1,2,3, and give `b` payoff `0` whenever it is absent and `-1` whenever
it is present.  Then:

- the two three-faces carry identical square-free six-cycles;
- every `b`-edge points from the `b`-present face to the `b`-absent face;
- no directed four-cycle occurs, because all transverse edges have the same
  orientation and both horizontal copies agree;
- the punishment value of `b` is exactly zero: Never guarantees zero, and
  against all-Never opponents the best value is zero; and
- at every induced-game Nash point with `b` fixed at Quit, the prescribed
  payoff of `b` is `-1`, while its owner continuation expression is zero.

Thus the persistent-base excess is identically `1` on the induced Nash set,
an exact instance of residual (15.2), but the table has no hidden oriented
square of the form (9.1).

These regressions need not satisfy the full global hard residual; in
particular some off-cycle pure coalitions can be sinks.  They prove the exact
logical boundary: neither semialgebraic residual nor the no-root statement
contains a square consumer by itself.  The full terminal witness may force
additional outgoing edges at those sinks, but a new argument must retain
their ancestry and show that they close a singleton-base four-cycle.  Finite
graph recurrence alone discards precisely that information.

## 13. Updated next question

The remaining useful target is the externality alternative (10.6), with the
source square still attached.  Does positive global minimum debt turn the
observer gain

```text
R_b({a,c})-R_b({b})>0
```

or its `{a,b,c}` version into an actual paid response at one of the two dates?
Without such a semantic adapter, the sure-anchor chamber yields the exact
finite dispatch (10.7) but does not close arbitrary strict-toggle cycles.
