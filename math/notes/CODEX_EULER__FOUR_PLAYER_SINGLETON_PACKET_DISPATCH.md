# Four-player support-two dispatch: eliminate the collision rate

Author: `CODEX_EULER`

Status: `ACTIVE; SECTIONS 2--15, 18--20, 21.1, 22--29.2, 31--32, AND 36--37 INDEPENDENTLY REVIEWED VALID; SECTION 38 SELF-AUDITED/AWAITING REVIEW; SECTIONS 16--17 AND 20.2--21 AUXILIARY; SECTION 33 INTERNAL CHECKED-BACKGROUND AUDIT; SECTION 34 SELF-AUDITED/AWAITING REVIEW; SECTION 35 SUPERSEDED BY SECTION 36`

Independent review:
[`CODEX_CEDAR`](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_CEDAR.md),
[`CODEX_RAMSEY`, Section 15](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_15.md).
[`CODEX_RAMSEY`, Section 18](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTIONS_18_1_18_2.md).
[`CODEX_RAMSEY`, Section 19](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTIONS_19_1_19_2.md).
[`CODEX_RAMSEY`, Section 20](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTIONS_20_1_20_2.md).
[`CODEX_RAMSEY`, Section 21](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_21.md).
[`CODEX_RAMSEY`, Section 22](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_22.md).
[`CODEX_RAMSEY`, Section 23](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_23.md).
[`CODEX_RAMSEY`, Section 24](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_24.md).
[`CODEX_RAMSEY`, Section 24.2](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_24_2.md).
[`CODEX_RAMSEY`, Section 24.3](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_24_3.md).
[`CODEX_RAMSEY`, Section 25](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_25.md).
[`CODEX_RAMSEY`, Section 26](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_26_1.md).
[`CODEX_RAMSEY`, Section 26 export gate](../feedback/LARGE_PERSISTENT_BASE_FINITE_NASH_DISPATCH__BY_CODEX_RAMSEY.md).
[`CODEX_RAMSEY`, Section 27](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_27.md).
[`CODEX_RAMSEY`, Section 27 export gate](../feedback/PURE_PAID_BASE_LEAVE_DESCENT__BY_CODEX_RAMSEY.md).
[`CODEX_RAMSEY`, Section 28.1](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_28_1.md).
[`CODEX_RAMSEY`, Sections 28.2--28.3](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTIONS_28_2_28_3.md).
[`CODEX_RAMSEY`, Section 28.4](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_28_4.md).
[`CODEX_RAMSEY`, Section 29.1](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_29_1.md).
[`CODEX_RAMSEY`, Section 29.2](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_29_2.md).
[`CODEX_RAMSEY`, Section 31](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_31.md).
[`CODEX_CEDAR`, Section 32](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_CEDAR__SECTION_32.md).
[`CODEX_RAMSEY`, Section 36](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_36.md).
[`CODEX_RAMSEY`, Section 37](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_37.md).

## Current result

For the crossed support-two chamber, the sure-blocker collision-repair search
can be reduced to a finite relabeling-invariant sign dispatch.  Away from two
pair-payoff equality hyperplanes, no interior rate is possible at all.  A
counterexample witness must therefore lie in one of three explicit
nonsingleton join-obstruction chambers.  On either equality hyperplane, the
remaining rate question is exactly feasibility of three affine inequalities
on `[0,1]`, for which a quantifier-free endpoint/cross-product criterion is
given below.

This is an ordinary mathematical reduction.  It neither closes the crossed
chamber nor claims that the residual data are inhabited by a genuine
counterexample.

The post-export strict-toggle analysis now adds the following independently
reviewed ordinary mathematics.  Every four-cycle face has an explicit exact
stationary/sure-blocker compiler test.  Every longer cycle with nonempty
intersection reduces to a finite induced binary-game Nash cell plus named
base-leave/outsider-join tests.  Empty-base cycles have an exact polynomial
stationary screen, and nonempty open compiler chambers have been constructed
inside all five three-face six-cycle geometries and one genuinely
four-dimensional eight-cycle geometry, including exact crossed-packet
incidence examples.

Propositions 14.1--14.3 are independently reviewed valid: an exact five-shape
six-cycle collector, explicit open chambers for all five shapes, and a general
open-chamber availability theorem for every finite empty-base cycle pattern.
The last theorem is not an
arbitrary-cycle consumer: the reward magnitudes are selected to meet the
stationary Bellman equations.  The complementary semialgebraic producer
problem remains open.

Sections 15--17 sharpen the complementary side, but only in a precisely
limited sense.  Proposition 15.1 gives the maintained static cycle a genuine
finite semantic dispatch into compiler tests or two named semialgebraic
residuals.  If an attempted stationary-root sequence in the empty-base
residual has defects tending to zero, it must escape to a boundary root with
at most one positive hazard; the subsequent sections classify that
conditional boundary.  The static cycle does **not** itself supply such a
vanishing-defect sequence, so this boundary classification does not close or
further shrink the full no-interior-solution residual.  Proposition 15.1 and
Corollary 15.2 are independently reviewed valid; the later auxiliary boundary
claims are still under review.

## 1. Exact question and checked inputs

Let the four players be distinct `a,b,c,d`.  Let `packet` be a
`QuittingNormalizedSingletonSourcePacket reward` with support `{a,b}`.  Under
a `QuittingTerminalExploitabilityWitness`, after possibly swapping `c,d`, the
checked support theorem gives

```text
r_a(c) < r_c(c) < r_b(c),
r_b(d) < r_d(d) < r_a(d).                         (1.1)
```

Here `r_S(i)` denotes player `i`'s reward at first-quitter coalition `S`.
Packet pinning and singleton-mixture feasibility also give

```text
r_a(a) <= r_b(a),       r_b(b) <= r_a(b),
chi_a <= r_a(a),        chi_b <= r_b(b),           (1.2)
```

where `chi_i` is the exact punishment value.

The two new checked residual screens add the following data.  If `g>0` is the
terminal exploitability gap, then

```text
r_a(a) <= -g   or   r_a(c)+g <= r_c(c),
r_b(b) <= -g   or   r_b(d)+g <= r_d(d).              (1.3)
```

Thus each supported owner is either quantitatively negative or is preempted,
by the full gap, by the outsider harmed by that owner's singleton row.  These
are four finite singleton subcases (`NN, NP, PN, PP`).

There is also an orthogonal projective-Q screen.  If a nonprojective
normalized-solo principal set `P` is supplied, then

```text
P != {a,b},       P != {a,d},       P != {b,c}.      (1.4)
```

Consequently, conditional on `|P|=2`, only `{a,c}`, `{b,d}`, or `{c,d}`
remain.  No size-two principal is assumed to exist.

For an ordered pair `(x,y)` of supported players, the checked collision repair
uses owner `x`, sure blocker `y`, and owner quit rate `p in [0,1]`.  Its exact
conditions are `QuittingCollisionOwnerOptimal`,
`QuittingCollisionSpectatorNoJoin`, and
`QuittingCollisionBlockerBalance`; by
`quittingCollisionRepairWorks_iff`, these are necessary and sufficient for
the all-behavior repair mechanism.

Sources inspected:

- `UniformEquilibrium/Quitting/Classification/ThreePlayer/AnalyticPacket.lean`:
  `QuittingNormalizedSingletonSourcePacket`;
- `UniformEquilibrium/Quitting/Classification/SingletonPacketSupport.lean`:
  `exists_uniformEquilibriumPayoff_of_support_eq_pair_of_first_noHarm` and the
  exact support-two formulas;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/Support.lean`:
  `exists_crossedSpectators_of_finFour_support_eq_pair`,
  `supportOwners_negative_or_crossedSpectators_preempt`, and
  `nonprojectivePrincipal_ne_safePairs_of_support_eq_pair`;
- `UniformEquilibrium/Quitting/Boundary/Repair/CollisionRepairCharacterization.lean`:
  the three repair predicates and `quittingCollisionRepairWorks_iff`;
- `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`:
  `quittingInstantPunishmentεEquilibriumExistence_of_collisionRepair`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/CollisionRepairScreen.lean`:
  `collisionRepair_condition_failure`;
- `UniformEquilibrium/Quitting/Stationary/MinMax.lean`:
  `quittingPunishmentValue_le_max_solo`;
- `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`:
  `isQuittingSureExitSet_iff_forall_max` and its unrestricted-behavior
  terminal-Nash compiler.

## 2. Owner optimality purifies the rate

Fix an orientation `(x,y)` and write

```text
O_0 = r_y(x),        O_1 = r_{x,y}(x),
Delta_x^y = O_1-O_0.
```

The owner's prescribed payoff is `(1-p)O_0+pO_1`.  Hence owner optimality is

```text
max(O_0,O_1) <= (1-p)O_0+pO_1.                    (2.1)
```

### Lemma 2.1 (rate purification)

For `0<=p<=1`, (2.1) holds exactly in the following cases:

```text
Delta_x^y < 0  => p=0,
Delta_x^y > 0  => p=1,
Delta_x^y = 0  => every p is owner-optimal.        (2.2)
```

Proof.  If `O_1>O_0`, subtracting `O_0` from (2.1) gives
`O_1-O_0 <= p(O_1-O_0)`, hence `p>=1`.  The opposite strict sign similarly
forces `p<=0`.  Equality of endpoints makes (2.1) an identity.  This uses no
packet hypothesis.  In particular a generic collision repair is necessarily
a sure singleton exit or a sure pair exit; a genuinely mixed exact row lives
on a pair-payoff equality hyperplane.

## 3. The remaining constraints are three affine endpoint tests

Let `z,t` be the two spectators.  Define for `s in {z,t}`

```text
A_s^0(x,y) = r_{s,y}(s)-r_y(s),
A_s^1(x,y) = r_{x,s,y}(s)-r_{x,y}(s),              (3.1)
```

and for the blocker

```text
A_y^0(x,y) = chi_y-r_y(y),
A_y^1(x,y) = r_x(y)-r_{x,y}(y).                    (3.2)
```

The packet gives `A_y^0(x,y)<=0` for either supported blocker.  After owner
optimality, all remaining collision-repair conditions are precisely

```text
(1-p) A_j^0(x,y)+p A_j^1(x,y) <= 0
for j in {z,t,y}.                                  (3.3)
```

The two spectator rows are exactly no-join.  Equation (3.2) is the checked
blocker-balance identity after moving the prescribed payoff to the right.

Consequently:

```text
Delta_x^y < 0:
  a repair exists iff A_z^0<=0 and A_t^0<=0;        (3.4)

Delta_x^y > 0:
  a repair exists iff A_z^1<=0, A_t^1<=0,
                         and A_y^1<=0.              (3.5)
```

The omitted blocker inequality in (3.4) is automatic from the packet.

## 4. Quantifier-free equality-face test

The equality case requires only the following elementary one-dimensional
lemma.  It is stated for a finite index set because it may be reusable by
other finite repair rows.

### Lemma 4.1 (affine interval feasibility)

For finitely many endpoint pairs `(u_j,v_j)`, there exists `p in [0,1]` with

```text
(1-p)u_j+p v_j <= 0   for every j                  (4.1)
```

if and only if both conditions hold:

1. for every `j`, `u_j<=0` or `v_j<=0`;
2. whenever

   ```text
   u_i>0>=v_i     and     u_j<=0<v_j,
   ```

   one has

   ```text
   u_i*v_j <= v_i*u_j.                              (4.2)
   ```

Proof.  A row with `u>0>=v` imposes the lower bound
`p>=u/(u-v)`, while a row with `u<=0<v` imposes the upper bound
`p<=-u/(v-u)`.  Rows with both endpoints nonpositive impose no restriction;
rows with both endpoints positive are impossible.  The denominators in the
lower and upper bounds are positive, and cross multiplication says that every
lower bound is at most every upper bound exactly when (4.2) holds.  Taking the
largest lower bound and smallest upper bound proves sufficiency.  The weak
zero-endpoint cases are included: they force `p=1` or `p=0` respectively.

Apply this to the three pairs `(A_j^0,A_j^1)` from Section 3.  Thus on
`Delta_x^y=0`, collision feasibility has an exact finite Boolean description
using only signs and quadratic cross products.  No existential rate remains;
a witness rate can be chosen as the maximum of the finitely many lower
thresholds.

## 5. Generic crossed-chamber dispatch

Return to support `{a,b}` and put

```text
alpha = r_{a,b}(a)-r_b(a),
beta  = r_{a,b}(b)-r_a(b).                          (5.1)
```

For the two spectators define the three maximum join defects

```text
J_b  = max_s [r_{s,b}(s)-r_b(s)],
J_a  = max_s [r_{s,a}(s)-r_a(s)],
J_ab = max_s [r_{a,b,s}(s)-r_{a,b}(s)],             (5.2)
```

where `s` ranges over `{c,d}`.

Assume first `alpha*beta != 0`.  Combining Lemma 2.1 with the blocker endpoint
in the opposite orientation gives the following finite alternative:

```text
alpha < 0  and J_b <= 0  => rate-0 repair (a,b),
beta  < 0  and J_a <= 0  => rate-0 repair (b,a),
alpha > 0, beta > 0, J_ab <= 0
                           => rate-1 pair repair.   (5.3)
```

The rate-one conclusion is independent of orientation: `alpha,beta>=0` are
the two members' no-leave inequalities and `J_ab<=0` is both spectators'
no-join inequality.

Therefore, under a terminal exploitability witness, the generic residual is
forced into the exact sign chamber

```text
alpha < 0  => J_b  > 0,
beta  < 0  => J_a  > 0,
alpha > 0 and beta > 0 => J_ab > 0.                 (5.4)
```

These implications also suffice to defeat both support-owner collision
orientations in the generic chamber:

- two negative signs force the two rate-zero repairs and (5.4) blocks them;
- mixed signs force one rate-zero repair, while the rate-one orientation is
  defeated by the other supported player's negative pair endpoint; and
- two positive signs force the common sure-pair repair, which `J_ab>0`
  defeats.

If exactly one of `alpha,beta` vanishes, use Lemma 4.1 for the corresponding
indifferent owner and the endpoint test for the other orientation.  If both
vanish, use Lemma 4.1 for both orientations.  This is a finite
lower-dimensional residual, not an unanalysed continuum of rates.

### 5A. Intersection with the checked singleton and principal screens

The owner alternatives (1.3) and collision defects (5.4) use disjoint reward
layers and must be intersected, not identified.  The complete generic
counterexample residual first chooses one of

```text
NN: r_a(a)<=-g and r_b(b)<=-g,
NP: r_a(a)<=-g and r_b(d)+g<=r_d(d),
PN: r_a(c)+g<=r_c(c) and r_b(b)<=-g,
PP: r_a(c)+g<=r_c(c) and r_b(d)+g<=r_d(d),           (5A.1)
```

and then imposes the applicable join defects from (5.4).  There is no direct
algebraic implication between them: (5A.1) contains only singleton rows,
whereas `J_a,J_b,J_ab` contain pair/triple rows.

The negative alternatives do add exact toggle anchors:

```text
r_a(a)<=-g  gives {a} -> empty,
r_b(b)<=-g  gives {b} -> empty.                      (5A.2)
```

The preemption alternatives add gap-labelled singleton-preemption edges
`a -> c` and `b -> d`.  These compare two different singleton coalitions and
are **not** one-player membership toggles on the coalition cube, so they are
not silently inserted into Proposition 9.1's toggle cycle.

The principal screen (1.4) is also conditional and orthogonal.  If a supplied
nonprojective principal happens to have size two, refine every case above by

```text
P in {{a,c},{b,d},{c,d}}.                            (5A.3)
```

No principal set, and no size-two conclusion, follows from the toggle
reduction.  Equations (5A.1)--(5A.3) therefore give a finite product dispatch:
four owner/preemption cases, the collision sign cases, and—only when present—
three possible hard principal pairs.

The construction is relabeling-invariant: compute (5.1)--(5.2) for the
unordered support pair, test both ordered orientations, and treat the two
players in its complement symmetrically through maxima.

## 6. Exact finite dispatch

The resulting support-two dispatch is:

1. If one supported singleton is no-harm for both outsiders, use
   `exists_uniformEquilibriumPayoff_of_support_eq_pair_of_first_noHarm`.
2. Otherwise, under a counterexample witness select the crossed spectators by
   `exists_crossedSpectators_of_finFour_support_eq_pair`.
3. Compute both oriented collision arrays from (3.1)--(3.2).  If either passes
   (3.4), (3.5), or Lemma 4.1, return its explicit legal rate and the checked
   collision-repair compiler input.
4. Otherwise return the crossed collision residue: (1.1), together with the
   quantifier-free failure formula for both orientations.  Generically this
   is exactly (5.4); on the equality faces it is the negation of Lemma 4.1's
   finite sign/cross-product criterion.

Step 4 is strictly smaller than the crossed singleton chamber because it adds
pair/triple reward and punishment-value constraints.  It is not the
conjecture under another name: every field is a displayed scalar table entry,
one exact punishment value, or a finite polynomial/sign comparison.

## 7. Packet-interface boundary example

There is a general completion freedom behind the example.  Once `mass`,
`target`, and the singleton rows satisfy every packet field except the
punishment floor, the extra inequalities

```text
max(r_i(i),0) <= target(i)   for every i             (7.1)
```

make that floor automatic for **every** completion of the nonsingleton reward
rows, by `quittingPunishmentValue_le_max_solo`.  Thus in this subclass the
packet axioms impose literally no pair/triple restriction.  A crossed-chamber
closure must use the counterexample-witness consequences or another global
compiler input, not an unstated packet constraint.

The collision residue is therefore nonempty at the packet interface.  Take
all four own singleton rewards to be zero and set

```text
r_a(c)=-1, r_b(c)= 1,
r_a(d)= 1, r_b(d)=-1,
```

with all other singleton coordinates zero.  Let `mass(a)=mass(b)=1/2`, all
other masses zero, and `target=0`.  Then every packet mixture inequality is an
equality, positive masses pin the target, and
`chi_i<=max(r_i(i),0)=0=target(i)` supplies every punishment floor.

Choose arbitrary real parameters `alpha,beta`.  Set all nonsingleton rewards
to zero except

```text
r_{a,b}(a)=alpha,      r_{a,b}(b)=beta,
r_{a,b,c}(c)=1,       r_{a,b,d}(d)=1.               (7.2)
```

These parameters are exactly the pair-endpoint differences in (5.1).  In
orientation `(a,b)`, spectator `d` has endpoint join defects `1` and `1`, so
its affine defect is `(1-p)+p=1` for every `p`.  In orientation `(b,a)`,
spectator `c` has the symmetric property.  Thus every rate for both ordered
collision repairs fails spectator no-join, for every pair-sign chamber and
on both equality faces.

This game has the exact all-Never equilibrium, because all own singleton
rewards are zero.  The family is therefore only an exact packet-interface
separation, not a terminal counterexample witness.  Its role is to show that
the nonsingleton residual in Step 4 is genuine, is not confined to the
equality faces, and cannot be deleted using the packet axioms.

Moreover this failure is relatively open in the nonsingleton completion:
both defeating spectator defects equal `1`, so all sufficiently small changes
of the involved pair/triple coordinates preserve their strict positivity.
By choosing `alpha,beta` in any prescribed nonzero sign chamber, one obtains
a relatively open family in every generic case of Section 5.  Thus the
support-owner collision repair is not merely missing on a thin algebraic
exceptional set of packet completions.

For any putative gap `0<g<=1`, the singleton rows of this family already
satisfy the `PP` inequalities in (5A.1): `c` preempts `a` and `d` preempts
`b` by at least `g`.  Hence even the strongest two-preemption branch of the
new owner screen does not determine any of the collision join defects.  This
is still only an interface-independence test, since the family has all-Never.

## 8. Promote every join obstruction to a sure-exit candidate

The profitable joins in (5.4) are not merely negative screens.  Each gives a
larger coalition in which the newly added member's retention inequality is
already strict.

### Lemma 8.1 (one-step join promotion)

Let `S` be a nonempty coalition, let `s notin S`, and suppose

```text
r_{S union {s}}(s) > r_S(s).                        (8.1)
```

Put `T=S union {s}`.  Then at least one of the following finite outputs is
available (the first occurs exactly when neither kind of strict failure
occurs):

1. `T` is a checked sure exit set and its pure root is an exact terminal Nash
   equilibrium against unrestricted behavioral deviations;
2. some old member `i in S` strictly gains by leaving,

   ```text
   r_{T\{i}}(i) > r_T(i);                            (8.2)
   ```

3. some remaining outsider `j notin T` strictly gains by joining,

   ```text
   r_{T union {j}}(j) > r_T(j).                      (8.3)
   ```

Proof.  By (8.1), the new member `s` strictly prefers staying in `T` to
leaving it.  If neither (8.2) nor (8.3) occurs, every old member weakly
prefers staying and every remaining outsider weakly prefers not joining.
Together with the strict condition for `s`, these are exactly the membership
toggle inequalities in `isQuittingSureExitSet_iff_forall_max`.

Under a terminal exploitability witness, output 1 is impossible, so every
positive join edge gives one of the explicit strict toggles (8.2)--(8.3).

### Corollary 8.2 (second-level generic dispatch)

Apply Lemma 8.1 to each positive defect selected in (5.4).

- If `alpha<0` and `s` satisfies
  `r_{b,s}(s)>r_b(s)`, then either `{b,s}` is a sure exit set or one of

  ```text
  r_s(b) > r_{b,s}(b),
  r_{a,b,s}(a) > r_{b,s}(a),
  r_{b,s,t}(t) > r_{b,s}(t)                          (8.4)
  ```

  holds, where `t` is the other spectator.  These are respectively blocker
  `b` leaving, supported outsider `a` joining, or the remaining spectator
  joining.

- If `beta<0`, the symmetric statement holds with `a,b` exchanged.

- If `alpha,beta>0` and `s` satisfies
  `r_{a,b,s}(s)>r_{a,b}(s)`, then either `{a,b,s}` is a sure exit set or

  ```text
  r_{b,s}(a) > r_{a,b,s}(a),
  r_{a,s}(b) > r_{a,b,s}(b),
  r_{a,b,s,t}(t) > r_{a,b,s}(t).                    (8.5)
  ```

  The new member `s` cannot be the leaving witness because its retention is
  already strict in the other direction.

This is again relabeling-invariant: apply the statement to every spectator
realizing the positive maximum, and return a sure set if any candidate passes;
otherwise retain all corresponding finite toggle obstructions.  It strictly
refines the generic residue with pair/triple/grand-coalition signs, but it does
not yet compile a toggle cycle.

## 9. The residual has an anchored finite strict-toggle cycle

### Proposition 9.1 (finite cycle dispatch)

Under a terminal exploitability witness, every generic residual output in
(5.4) supplies:

1. one of the displayed strict join edges from a supported singleton or the
   supported pair;
2. a finite directed strict-toggle path starting with that edge; and
3. a reachable simple directed toggle cycle of even length in
   `{4,6,8,10,12,14,16}`.

Every edge is labelled by one player and one exact reward comparison

```text
S -> S triangle {i},
r_{S triangle {i}}(i) > r_S(i).                     (9.1)
```

Proof.  Include the empty coalition with its extended reward zero.  A terminal
counterexample witness rules out every sure exit set, including the empty
set, because the checked pure-set compiler would otherwise give an exact
terminal Nash equilibrium.  Therefore at every coalition `S` at least one
membership-toggle inequality fails strictly, producing an outgoing edge
(9.1).  Begin with the strict join edge supplied by (5.4) and repeatedly
choose an outgoing strict toggle.  There are only `2^4=16` coalitions, so a
vertex repeats; deleting the preperiod and then shortening at the first repeat
gives a simple directed cycle reachable from the anchored edge.

The coalition hypercube is bipartite by parity of cardinality, so the cycle
length is even.  Length two would traverse the same toggle comparison in both
strict directions, which is impossible.  A simple cycle has length at most
sixteen, proving the list.

This is a genuinely finite relabeling-invariant residual dispatch: modulo the
finite action of `S_4`, there are only finitely many anchored path/cycle
patterns, and each pattern consists solely of strict polynomial table
inequalities (with the empty reward fixed at zero).  It is still not a
positive compiler.  An arbitrary strict coalition-toggle cycle need not meet
the Bellman balance, hazard, or passive-player inequalities of the checked
open-sign cyclic producers.

## 10. A blocker-anchored four-cycle compiles with two extra checks

The first nontrivial cycle shape has a genuine existing consumer.  Let `b,s,t,a`
be the four distinct players.  Suppose the strict toggle cycle is

```text
{b} -> {b,s} -> {b,s,t} -> {b,t} -> {b}.            (10.1)
```

Equivalently, define

```text
g_s^0 = r_{b,s}(s)-r_b(s)             > 0,
g_s^1 = r_{b,s,t}(s)-r_{b,t}(s)       < 0,
g_t^0 = r_{b,t}(t)-r_b(t)             < 0,
g_t^1 = r_{b,s,t}(t)-r_{b,s}(t)       > 0.           (10.2)
```

Set

```text
q = g_s^0/(g_s^0-g_s^1),
p = -g_t^0/(g_t^1-g_t^0).                           (10.3)
```

All denominators are positive and `0<p,q<1`.  Let `x` be the product root at
which `b` Quits surely, `s` Quits with probability `p`, `t` Quits with
probability `q`, and `a` Continues.  Put

```text
w00=(1-p)(1-q),  w10=p(1-q),
w01=(1-p)q,      w11=pq,

V_i = w00 r_b(i)+w10 r_{b,s}(i)
        +w01 r_{b,t}(i)+w11 r_{b,s,t}(i).            (10.4)
```

### Proposition 10.1 (sure-blocker matching-pennies compiler)

Assume, in addition to (10.2), the spectator inequality

```text
w00 r_{a,b}(a)+w10 r_{a,b,s}(a)
  +w01 r_{a,b,t}(a)+w11 r_{a,b,s,t}(a) <= V_a,       (10.5)
```

and the blocker balance

```text
p(1-q)r_s(b)+(1-p)q r_t(b)+pq r_{s,t}(b)
  +(1-p)(1-q)chi_b <= V_b.                           (10.6)
```

Then `V` is a uniform-equilibrium payoff.  More precisely, the fixed root
`x`, followed after all-Continue by an accuracy-dependent stationary
near-minmax punishment of `b`, is a terminal `epsilon`-Nash profile for every
`epsilon>0` against unrestricted behavioral deviations.  This instantiates
the checked `QuittingInstantPunishmentεEquilibriumExistence` branch with sure
quitter `b`.

Proof.  Player `s`'s Quit-minus-Continue value against `t`'s probability `q`
is

```text
(1-q)g_s^0+q g_s^1=0                                (10.7)
```

by (10.3).  Player `t`'s corresponding difference is

```text
(1-p)g_t^0+p g_t^1=0.                               (10.8)
```

Thus both actions of both mixers pay exactly their prescribed coordinates in
(10.4).  Because `b` Quits surely, an arbitrary behavioral deviation by `s`
or `t` reduces to its date-zero action mixture; (10.7)--(10.8) control the
full deviation class, not merely stationary deviations.

The same absorption makes player `a`'s only relevant choice Continue versus
joining at date zero.  Inequality (10.5) is exactly its no-join condition.

For a given `epsilon>0`, choose a stationary punishment row whose unilateral
cap for `b` is at most `chi_b+epsilon`.  If `b` Quits at date zero it receives
exactly `V_b`.  If it Continues, the three absorbing outcomes of the two
mixers contribute the first three terms of (10.6); only their joint-Continue
event reaches the punishment.  Hence every continuation deviation of `b`
pays at most the left side of (10.6) plus
`(1-p)(1-q)epsilon<=epsilon`, and therefore at most `V_b+epsilon`.
An arbitrary date-zero randomization is a convex combination of Quit and
Continue.

The first row absorbs because `b` Quits surely, so its terminal payoff is the
fixed vector `V`, independent of the punishment accuracy.  The existing
terminal fixed-target selection theorem now gives the asserted uniform
payoff.  This proves the proposition.

### Residual from this cycle shape

Under a terminal exploitability witness, a reachable cycle of the form (10.1)
must therefore satisfy the exact finite disjunction

```text
spectator join value in (10.5) > V_a
or
blocker continuation value in (10.6) > V_b.         (10.9)
```

Thus this whole cycle pattern has been matched to an all-behavior compiler;
only its two explicit failure chambers remain.  The construction is invariant
under relabeling of the persistent blocker and the two alternating togglers.

### Proposition 10.2 (two-blocker four-cycle compiler)

Every simple four-cycle of the coalition cube is a two-dimensional face: two
players toggle and the other two coordinates remain fixed.  The case in which
both fixed players are present has an even simpler compiler.

Let the fixed base be `B={a,b}` and suppose

```text
B -> B union {s} -> B union {s,t} -> B union {t} -> B
```

has the same strict matching-pennies signs as (10.2), with every occurrence of
`{b}` replaced by `B`.  Define `p,q,w00,w10,w01,w11` by (10.3)--(10.4), now
using the four base coalitions.  Let both `a,b` Quit surely and let `s,t` use
the interior probabilities.

If the two base-member leave inequalities

```text
sum_(R subset {s,t}) w_R r_{({b} union R)}(a) <= V_a,
sum_(R subset {s,t}) w_R r_{({a} union R)}(b) <= V_b                 (10.10)
```

hold, this fixed product root is an exact terminal Nash profile against all
behavioral deviations, and `V` is a uniform-equilibrium payoff.

Proof.  The two togglers are indifferent by the same affine calculations
(10.7)--(10.8).  If either base player deviates, the other still Quits surely,
so only the deviator's date-zero membership decision is relevant; (10.10)
controls it.  The root absorbs surely even after any one player's deviation.
Thus no punishment continuation is needed.  Under a terminal witness, at
least one inequality in (10.10) must fail.

Consequently, every reachable four-cycle whose fixed base is nonempty now has
an explicit all-behavior compiler test: Proposition 10.1 for base size one and
Proposition 10.2 for base size two.  The only four-cycle face without a sure
fixed quitter has empty base; that stationary/self-returning shape remains
to be treated next.

### Proposition 10.3 (empty-base stationary four-cycle compiler)

Suppose the remaining face is

```text
empty -> {s} -> {s,t} -> {t} -> empty,              (10.11)
```

and write

```text
A=r_s(s),       B=r_t(s),       C=r_{s,t}(s),
D=r_t(t),       E=r_s(t),       F=r_{s,t}(t).
```

The strict cycle gives

```text
A>0,       B>C,       F>E,       D<0.               (10.12)
```

Assume the two additional interval inequalities

```text
A>B>C,                   F>E>D.                     (10.13)
```

Define

```text
q=(A-B)/(A-C),           p=(E-D)/(F-D),             (10.14)
```

so `0<p,q<1`.  Let the root make `s` Quit with probability `p`, `t`
Quit with probability `q`, and the other two players `a,b` Continue.  Put

```text
delta = p(1-q)+(1-p)q+pq = 1-(1-p)(1-q),

U_i = [p(1-q)r_s(i)+(1-p)q r_t(i)+pq r_{s,t}(i)]/delta.   (10.15)
```

For each passive player `i in {a,b}`, define its immediate-join value

```text
J_i=(1-p)(1-q)r_i(i)+p(1-q)r_{i,s}(i)
       +(1-p)q r_{i,t}(i)+pq r_{i,s,t}(i).           (10.16)
```

If

```text
J_a <= U_a,             J_b <= U_b,                 (10.17)
```

then the stationary repetition of this root is an exact terminal Nash
profile against unrestricted behavioral deviations, and `U` is a uniform-
equilibrium payoff.

Proof.  The root absorbs with probability `delta>0` on every live row, so
(10.15) is its literal terminal payoff.  For player `s`, the Quit endpoint is

```text
(1-q)A+qC=B,                                            (10.18)
```

by (10.14).  If `s` Continues, player `t` Quits with probability `q`; the
Continue endpoint at the claimed fixed point is

```text
qB+(1-q)U_s=B,
```

because the Bellman identity from (10.15) gives `U_s=B`.  Thus both actions
of `s` equal its prescribed payoff.  Symmetrically,

```text
(1-p)D+pF=E=U_t,
```

and both actions of `t` are optimal.  For a passive player `i`, Continue has
value `U_i`, while Quit immediately has value `J_i`; hence (10.17) is exactly
the endpoint Nash condition.

Every player's opponents contract strictly: `t` contracts the tail faced by
`s`, `s` contracts the tail faced by `t`, and both contract the tails faced by
`a,b`.  Therefore the checked stationary endpoint compiler upgrades these
one-row endpoint inequalities to exact terminal Nash against every behavioral
deviation, including arbitrary pure times and Never.  Reusing this same exact
terminal profile at every requested accuracy, with its fixed payoff `U`, and
applying fixed-target terminal selection gives the uniform payoff.

Consequently an empty-base strict four-cycle under a terminal witness must
obey the finite residual disjunction

```text
A <= B   or   E <= D   or   J_a>U_a   or   J_b>U_b.  (10.19)
```

The other halves `B>C` and `F>E` are already forced by the cycle.  Thus every
simple four-cycle face now has an explicit all-behavior compiler test and a
finite failure chamber.  This does not compile a failure chamber or a longer
toggle cycle.

Sources additionally inspected:

- `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`:
  `QuittingInstantPunishmentεEquilibriumExistence` and
  `exists_punishRow_stationaryUnilateralCap_le`;
- `UniformEquilibrium/Quitting/Classification/InstantPunishmentEquivalence.lean`:
  the unrestricted constant-row/profile-punishment equivalence;
- `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`:
  `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` and the
  exact fixed-point endpoint compiler;
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`:
  the fixed-target terminal selection theorem.

## 11. Every cycle with a persistent base reduces to a finite normal-form test

The preceding four-cycle calculations are instances of a more general
compiler which also captures a nontrivial class of the longer cycles.

Let the player set be partitioned as

```text
I = B disjoint-union F disjoint-union O,      B nonempty.           (11.1)
```

Players in `B` are fixed Quitters, players in `F` are the free coordinates of
a cube face, and players in `O` are fixed outsiders.  Consider the finite
binary-action game on `F` in which a pure action set `R subset F` gives player
`f in F` the payoff `r_{B union R}(f)`.  Choose a mixed Nash equilibrium `x`
of this finite game, and let `mu(R)` be its product distribution on subsets of
`F`.  Such an `x` always exists by the finite Nash theorem.  Define

```text
V_i = sum_(R subset F) mu(R) r_{B union R}(i).        (11.2)
```

For an outsider `o in O`, define

```text
J_o = sum_(R subset F) mu(R) r_{B union R union {o}}(o).  (11.3)
```

### Proposition 11.1 (persistent-base face compiler)

If `|B|>=2` and

```text
J_o <= V_o                                      for every o in O,
sum_R mu(R) r_{(B\{b}) union R}(b) <= V_b       for every b in B,   (11.4)
```

then the product root in which `B` Quits surely, `F` plays `x`, and `O`
Continues is an exact terminal Nash profile against all behavioral deviations.

If `B={b}` and

```text
J_o <= V_o                                      for every o in O,
sum_(nonempty R subset F) mu(R) r_R(b)
  +mu(empty) chi_b <= V_b,                                           (11.5)
```

then, for every `epsilon>0`, that root followed after all-Continue by an
accuracy-dependent stationary near-minmax punishment of `b` is a terminal
`epsilon`-Nash profile with the same fixed payoff `V`.  In either case `V` is
a uniform-equilibrium payoff.

Proof.  Every player in `F` faces the finite game used to choose `x`: the
fixed base absorbs at date zero even after that free player deviates.  Thus
finite-game Nash controls every behavioral deviation, not just another
date-zero mixed action.  An outsider's only outcome-relevant choice is whether
to join at date zero, and (11.3)--(11.5) control that choice.

If `|B|>=2`, a deviating base member leaves another sure Quitter, so its only
outcome-relevant choice is membership at date zero and (11.4) applies.  If
`B={b}`, a deviation by `b` to Continue absorbs immediately on every
`R!=empty`; only `R=empty` reaches the punishment.  The last line of (11.5)
is therefore exactly the instant-punishment bound, up to the chosen
`epsilon`.  Nominal play always absorbs at the first row through `B`, so its
payoff is the fixed vector (11.2) for every punishment accuracy.  Fixed-target
terminal selection gives the uniform payoff.

### Finite residual for longer cycles

Let `C` be any reachable strict-toggle cycle and take

```text
B = intersection_(S in C) S,
F = (union_(S in C) S) \ B,
O = I \ (B union F).                                (11.6)
```

If `B` is nonempty, Proposition 11.1 applies to every Nash equilibrium of the
finite induced game on `F`.  Under a terminal exploitability witness, **each**
such equilibrium must violate at least one displayed base-leave or
outsider-join inequality.  This is a real restriction on six- and eight-cycles
with a persistent blocker, not an arbitrary-cycle compiler.

For four players the residual is finite semialgebraic.  There are at most
three free binary players, and their Nash set is obtained by the `3^|F|`
finite support-status cases `Quit`, `Continue`, or `mix`, followed by
multilinear indifference and weak endpoint inequalities in the mixing
probabilities.  The added tests (11.4)--(11.5)
are polynomial after clearing the product probabilities.  Thus a persistent-
base cycle returns either a compiler input or an explicit finite support cell
on which every induced Nash equilibrium fails a named base/outsider test.

Propositions 10.1 and 10.2 are the two-free-player instances with `|B|=1`
and `|B|=2`.  Proposition 11.1 does not use the strict cycle signs to guarantee
one preferred Nash support, and it makes no claim about cycles whose
intersection is empty.

### Corollary 11.2 (uniform residual gap on the induced Nash set)

Fix `B,F,O` and the reward table.  For an induced-game Nash equilibrium `x`,
let `G(x)` be the maximum of the outsider-join and base-leave excesses in
(11.4), or in (11.5) when `B` is a singleton.  Under a terminal
exploitability witness,

```text
gamma_(B,F) := min { G(x) : x is an induced-game Nash equilibrium } > 0.
                                                                    (11.7)
```

Indeed, the induced Nash set is nonempty and compact, and `G` is continuous.
Proposition 11.1 says `G(x)>0` at every point of that set; hence its attained
minimum is strictly positive.  Thus failure of the persistent-base compiler
is not merely pointwise selection failure: the entire induced Nash set is
separated from the legal base/outsider inequalities by a fixed positive
deviation gap.  This gap is face- and table-dependent; no bound in terms of
the original terminal witness gap is claimed.

### Corollary 11.3 (which cycle lengths can retain a base)

In the four-cube, a simple cycle with nonempty intersection has at most three
free coordinates, hence at most `2^3=8` vertices.  Therefore every reachable
cycle of length `10,12,14`, or `16` automatically has empty intersection.
After the complete four-cycle screen of Section 10, the only persistent-base
cycle lengths still needing the finite Nash-cell analysis of Proposition 11.1
are `6` and `8`, necessarily with a singleton base when all three free
coordinates are used.  This is purely a cube-dimension count and does not
claim those residual cells are empty.

## 12. Empty-base cycles have an exact polynomial stationary screen

For the remaining empty-intersection cycles, the stationary question can at
least be reduced to one explicit semialgebraic system rather than left as an
unspecified equilibrium search.

Let `F` be a set of at least two active players and let `O=I\F`.  Choose
variables

```text
0 < p_i < 1             (i in F).                   (12.1)
```

For `i in F`, let `mu_{-i}(R)` be the product probability that exactly
`R subset F\{i}` Quits.  Define

```text
d_i = sum_(nonempty R subset F\{i}) mu_{-i}(R),
N_i = sum_(nonempty R subset F\{i}) mu_{-i}(R) r_R(i),
Q_i = sum_(R subset F\{i}) mu_{-i}(R) r_{R union {i}}(i),
H_i = d_i Q_i-N_i.                                  (12.2)
```

All `d_i` are positive.  Let `mu(R)` be the full product probability on
`R subset F` and put

```text
delta = sum_(nonempty R subset F) mu(R),
U_k = [sum_(nonempty R subset F) mu(R) r_R(k)]/delta.  (12.3)
```

For every passive `o in O`, put

```text
J_o = sum_(R subset F) mu(R) r_{R union {o}}(o).     (12.4)
```

### Proposition 12.1 (interior stationary polynomial compiler)

If

```text
H_i=0              for every i in F,
J_o<=U_o           for every o in O,                (12.5)
```

then the stationary product root with rates `(p_i)_(i in F)` and all players
in `O` Continuing is an exact terminal Nash profile against unrestricted
behavioral deviations.  Its literal payoff is `U`, hence `U` is a uniform-
equilibrium payoff.

Proof.  For active `i`, `H_i=0` says

```text
Q_i=N_i/d_i.                                         (12.6)
```

The right side is the payoff from Continuing now, conditional on some other
active player eventually absorbing the current iid row.  More directly, if
`c_i=1-d_i`, then at the fixed point `Q_i` the Continue endpoint is

```text
N_i+c_i Q_i=Q_i.                                    (12.7)
```

Thus Quit and Continue are equal for every active mixer.  The stationary
Bellman equation and `delta>0` then identify this common value with the
literal terminal payoff `U_i` in (12.3).  A passive player's Continue endpoint
is its literal payoff `U_o`, while its Quit endpoint is exactly `J_o`.

Every player faces strict opponent contraction because at least two active
rates are positive.  The exact stationary endpoint compiler therefore turns
(12.5) into terminal Nash against arbitrary behavioral strategies, including
all pure times and Never.  Fixed-target terminal selection gives the uniform
payoff.

After multiplying each passive inequality by `delta>0`, (12.1)--(12.5) are a
finite polynomial equality/inequality system in the rates and reward-table
entries.  Consequently an empty-base strict-toggle cycle with active set `F`
returns one of two finite outputs:

1. a solution of (12.1)--(12.5), hence a checked stationary compiler input;
2. the exact semialgebraic residual that its vertex sign inequalities hold but
   this polynomial system has no solution.

For `|F|=2`, eliminating the two equations gives exactly (10.13)--(10.14).
For an empty-base six-cycle in a three-dimensional face, this is a system of
three explicit equations and one passive-player inequality.  For a genuinely
four-dimensional cycle it is four equations and no passive inequality.  No
existence of an interior solution follows merely from the directed cycle;
that is the next mathematical issue.

### Proposition 12.2 (a strict six-cycle need not meet the stationary screen)

There is an exact rational four-player table with the strict empty-base cycle

```text
empty -> {1} -> {1,2} -> {1,2,3} -> {2,3} -> {3} -> empty,  (12.8)
```

but with no interior solution of (12.2) on `F={1,2,3}`.  Define the following
payoff coordinates and set every unlisted coordinate to zero:

```text
player 1:  r_1(1)=1,
           r_2(1)=r_3(1)=r_{2,3}(1)=2;

player 2:  r_{1,2}(2)=1,       r_3(2)=1;

player 3:  r_{1,2,3}(3)=1,     r_3(3)=-1;

player 4:  zero on every coalition.                         (12.9)
```

The six edge comparisons in order are

```text
1>0,   1>0,   1>0,   2>0,   1>0,   0>-1.          (12.10)
```

Now write `x=p_2`, `y=p_3`.  For player `1`,

```text
d_1=x+y-xy,
N_1=2d_1,
Q_1=(1-x)(1-y),
H_1=d_1[(1-x)(1-y)-2] < 0                         (12.11)
```

throughout `0<x,y<1`.  Hence `H_1=0` is impossible, independently of
`p_1`.  The passive player `4` has `J_4=U_4=0`, so passive-player failure is
not responsible.

This exact example proves that strict toggle recurrence, even with a simple
six-cycle and a harmless passive player, does not force the interior
stationary compiler.  It is not a counterexample to equilibrium existence:
for example its singleton `{2}` is already a sure exit set.  Its sole role is
to separate the graph-sign input from the stationary Bellman equations and to
justify a genuinely periodic/block step in any further treatment of the
empty-base residual.

### Proposition 12.3 (balanced singleton-pair six-cycle compiler)

One nontrivial empty-base six-cycle subclass does satisfy Proposition 12.1.
Let the active players be `1,2,3`, let `o` be passive, and consider

```text
{1}->{1,2}->{2}->{2,3}->{3}->{1,3}->{1}.            (12.12)
```

Fix numbers `q_i` and `A_i>0`.  For each active player, require every reward
on a coalition containing that player to equal `q_i`.  On coalitions of the
other two players, set

```text
player 1: r_2(1)=q_1+A_1,  r_3(1)=q_1-A_1,
          r_{2,3}(1)=q_1;

player 2: r_3(2)=q_2+A_2,  r_1(2)=q_2-A_2,
          r_{1,3}(2)=q_2;

player 3: r_1(3)=q_3+A_3,  r_2(3)=q_3-A_3,
          r_{1,2}(3)=q_3.                            (12.13)
```

Then all six arrows in (12.12) are strict, with margins `A_2,A_1,A_3,
A_2,A_1,A_3` in order.  If all three active players use the same stationary
Quit probability `p in (0,1)`, then

```text
H_1=-A_1(p_2-p_3)=0,
H_2=-A_2(p_3-p_1)=0,
H_3=-A_3(p_1-p_2)=0.                                (12.14)
```

More generally, the displayed identities hold for arbitrary interior rates,
so the active stationary equations force exactly `p_1=p_2=p_3`.

Consequently, if for some `p in (0,1)` the passive inequality

```text
J_o(p,p,p) <= U_o(p,p,p),                            (12.15)
```

holds, Proposition 12.1 supplies an exact stationary terminal Nash profile
and a uniform-equilibrium payoff.  The active coordinates of that payoff are
exactly `(q_1,q_2,q_3)`.

Proof.  For player `1`, writing `x=p_2,y=p_3` and
`d=x+y-xy`, (12.13) gives

```text
Q_1=q_1,
N_1=q_1 d+A_1[x(1-y)-(1-x)y]
   =q_1 d+A_1(x-y).
```

Thus `H_1=-A_1(x-y)`; the other two identities follow cyclically.  The rest
is Proposition 12.1.  After multiplying (12.15) by the positive absorption
probability `1-(1-p)^3`, the remaining passive test is one explicit
one-variable polynomial inequality.  This is a genuine empty-base six-cycle
compiler subclass, but the balanced payoff identities (12.13) are additional
structure and are not implied by the toggle signs.

### Proposition 12.4 (an open six-cycle compiler chamber)

The preceding subclass can be made transverse, so the compiler is not
confined to a thin equality family.  Fix a rational `p_0 in (0,1)`.  For each
active player `i`, let `h(i)` be its high opponent and `l(i)` its low opponent
in the cycle (12.12):

```text
h(1)=2, l(1)=3;    h(2)=3, l(2)=1;    h(3)=1, l(3)=2.
```

Choose rational numbers

```text
a_i<0<b_i,
c_i=-(1-p_0)(a_i+b_i)/p_0,                           (12.16)
```

with

```text
product_i(-a_i) != product_i b_i.                    (12.17)
```

As before, give player `i` the constant payoff `q_i` on every active
coalition containing `i`, and set

```text
r_{h(i)}(i)=q_i-a_i,
r_{l(i)}(i)=q_i-b_i,
r_{h(i),l(i)}(i)=q_i-c_i.                            (12.18)
```

Then (12.12) is strict: leaving at the high context gains `-a_i>0`, and
joining at the low context gains `b_i>0`.  If `x=p_{h(i)}` and
`y=p_{l(i)}`, its stationary polynomial is exactly

```text
H_i=a_i x(1-y)+b_i(1-x)y+c_i xy.                     (12.19)
```

Equation (12.16) gives `H_i(p_0,p_0)=0`.  At the common-rate point,

```text
partial_x H_i=-b_i,          partial_y H_i=-a_i.     (12.20)
```

In the variable order `(p_1,p_2,p_3)`, the Jacobian has zero diagonal and
determinant

```text
product_i(-a_i)-product_i b_i != 0.                  (12.21)
```

Therefore the ordinary implicit-function theorem gives an open neighborhood
of the relevant reward-table entries in which a unique nearby interior rate
triple solves all three equations `H_i=0`.  If the passive inequality is
strict at the base table, it remains valid after shrinking the neighborhood.
Every table in that neighborhood is then accepted by Proposition 12.1.

This open chamber is nonempty.  For example take `p_0=1/2`, all `a_i=-1`,
and `(b_1,b_2,b_3)=(1,1,2)`.  Give the passive player payoff zero on every
coalition not containing it and payoff `-1` on every coalition containing it;
then `U_o=0>J_o=-1`.  All data are rational, (12.17) holds, and all six toggle
margins are strict.  Thus a full Euclidean-open family of empty-base strict
six-cycles, not only the balanced ray (12.13), is matched to the checked
stationary all-behavior compiler.

### Proposition 12.5 (packet support cannot occupy two active cycle labels)

The constant-containing subclass has a sharp intersection with the original
support-two packet.  If the packet support is `{a,b}`, its pin and mixture
feasibility imply

```text
r_b(a)>=r_a(a),              r_a(b)>=r_b(b).         (12.22)
```

In (12.18), for every pair of active cycle labels one of the two is the
other's low context.  For that ordered pair `(i,l(i))`,

```text
r_{l(i)}(i)=q_i-b_i < q_i=r_i(i).                   (12.23)
```

Therefore no two active labels in Proposition 12.4 can both belong to the
positive packet support.  In a four-player support-two instance, any use of
this six-cycle compiler must place exactly one supported owner among the three
active labels and the other supported owner at the passive coordinate; the
two remaining active labels are the crossed outsiders.

Proof.  If positive packet masses on `i,j` are `mu_i,mu_j`, the pinned
coordinate `v_i=r_i(i)` and singleton-mixture feasibility give

```text
mu_i r_i(i)+mu_j r_j(i) >= r_i(i),
```

hence `r_j(i)>=r_i(i)` because `mu_j>0` and `mu_i+mu_j=1`.  Apply this in both
directions and compare with (12.23).  The conclusion is only a support-label
restriction on this compiler chamber; it neither rules the chamber out nor
asserts the remaining packet and punishment-floor fields automatically.

### Proposition 12.6 (the open chamber genuinely meets the crossed packet)

The support restriction in Proposition 12.5 is sharp.  There is an exact
rational normalized singleton packet in the crossed `PP` chamber which is
accepted by Proposition 12.4.

Take active labels `1,2,3`, passive label `4`, common rate `p_0=1/2`,
`q_i=0`, `a_i=-2`, and `b_i=1` for all active `i`.  Thus `c_i=1` and the
Jacobian determinant in (12.21) is `8-1=7`.  The singleton reward vectors are

```text
r_1=( 0,-1, 2,0),       r_2=( 2,0,-1,1),
r_3=(-1, 2, 0,1),       r_4=( 0,1,-1,0).             (12.24)
```

On active nonsingleton coalitions, complete the active-player coordinates by
(12.18): every coordinate belonging to the quitting active player is zero,
and

```text
r_{2,3}(1)=r_{1,3}(2)=r_{1,2}(3)=-1.                (12.25)
```

Set every other active-player coordinate to zero.  For player `4`, put payoff
`1` on every nonempty active coalition except `r_1(4)=0`; put payoff `-1` on
every coalition containing `4` and at least one active player, while retaining
`r_4(4)=0`.

Let the packet mass be `1/2` on each of `{1,4}` and zero elsewhere, with
target `v=0`.  Averaging the two support singleton rows gives

```text
(r_1+r_4)/2=(0,0,1/2,0)>=v.                         (12.26)
```

The active pin holds at players `1,4`, every own singleton reward is zero, and
the generic bound `chi_i<=max(r_i(i),0)=0` gives all punishment floors.
Therefore these data satisfy the complete normalized singleton-packet
interface.

With support owners `(a,b)=(1,4)` and outsiders `(c,d)=(2,3)`, the crossed
rows are

```text
r_1(2)=-1 < r_2(2)=0 < r_4(2)=1,
r_4(3)=-1 < r_3(3)=0 < r_1(3)=2.                   (12.27)
```

Both quantitative owner screens use their preemption alternatives for every
`0<g<=1`.  At the stationary root `p_1=p_2=p_3=1/2`, the active payoffs are
zero.  Player `4` has

```text
U_4=(6/8)/(7/8)=6/7,
J_4=-7/8,                                             (12.28)
```

so the passive inequality is strict.  Proposition 12.4 therefore gives an
exact stationary terminal Nash profile and uniform payoff `(0,0,0,6/7)`.

This example proves that the open six-cycle compiler is not external to the
maintained packet branch: it occupies a genuine crossed, quantitatively
preempted packet subchamber.  It does not show that every nearby reward table
retains the same packet mass/target—the openness claim concerns the compiler
and strict cycle, while packet-interface incidence is witnessed exactly at
the displayed rational table.

## 13. An open empty-base eight-cycle chamber

The same calculation closes a genuinely four-dimensional cycle subclass with
no passive player.  Consider the singleton-pair cycle

```text
{1}->{1,2}->{2}->{2,3}->{3}->{3,4}->{4}->{1,4}->{1}.  (13.1)
```

For each `i`, define its high, low, and neutral opponents by

```text
h(1)=2,l(1)=4,n(1)=3;      h(2)=3,l(2)=1,n(2)=4;
h(3)=4,l(3)=2,n(3)=1;      h(4)=1,l(4)=3,n(4)=2.     (13.2)
```

Fix `p_0 in (0,1)`, `a_i<0<b_i`, and

```text
c_i=-(1-p_0)(a_i+b_i)/p_0.                           (13.3)
```

Give player `i` payoff `q_i` on every coalition containing `i`.  On a
nonempty opponent coalition `R`, make the neutral opponent irrelevant and set

```text
r_R(i)=q_i-a_i   if h(i) in R and l(i) notin R,
r_R(i)=q_i-b_i   if l(i) in R and h(i) notin R,
r_R(i)=q_i-c_i   if h(i),l(i) both belong to R,
r_R(i)=q_i       if neither belongs to R.            (13.4)
```

The last case can only be the neutral singleton.  The cycle (13.1) is strict,
with high-leave margins `-a_i` and low-join margins `b_i`.

### Proposition 13.1 (transverse eight-cycle compiler)

For arbitrary interior rates, the stationary polynomial for player `i` is

```text
H_i=a_i p_{h(i)}(1-p_{l(i)})
      +b_i(1-p_{h(i)})p_{l(i)}
      +c_i p_{h(i)}p_{l(i)},                         (13.5)
```

independent of the neutral rate.  Hence the common rate `p_i=p_0` solves all
four equations.  At that point, the Jacobian in variable order
`(p_1,p_2,p_3,p_4)` is

```text
[  0   -b_1    0   -a_1 ]
[ -a_2   0   -b_2   0   ]
[  0   -a_3    0   -b_3 ]
[ -b_4   0   -a_4   0   ],                          (13.6)
```

with determinant

```text
(b_1 b_3-a_1 a_3)(a_2 a_4-b_2 b_4).                (13.7)
```

If both factors in (13.7) are nonzero, the implicit-function theorem gives a
full open neighborhood of reward tables with a nearby interior solution of
all four stationary equations.  Proposition 12.1, now with no passive
inequality, compiles every table in that neighborhood to an exact stationary
terminal Nash profile and a uniform-equilibrium payoff.

Proof.  The baseline `q_i` contribution to the Continue numerator is
`q_i d_i`.  Summing over the neutral player's two actions leaves the excess

```text
-a_i p_h(1-p_l)-b_i(1-p_h)p_l-c_i p_h p_l
```

in `N_i-q_i d_i`, which is (13.5) after forming `H_i=d_iQ_i-N_i` and using
`Q_i=q_i`.  Equations (13.3), (13.6), and direct determinant expansion give
the rest.  Strict cycle margins and interiority persist after shrinking the
IFT neighborhood.

### Proposition 13.2 (exact crossed-packet incidence)

This open compiler also meets the maintained support-two branch in the most
natural label pattern.  Take `p_0=1/2`, every `q_i=0`, every `a_i=-2`, and
every `b_i=1`, so `c_i=1`; both determinant factors in (13.7) are nonzero.
The singleton reward matrix, displayed by coalition columns, is

```text
r_1=( 0,-1, 0, 2),       r_2=( 2,0,-1, 0),
r_3=( 0, 2, 0,-1),       r_4=(-1,0, 2, 0).           (13.8)
```

Let the packet mass be `1/2` on the opposite labels `{1,3}`, with target
zero.  Then

```text
(r_1+r_3)/2=(0,1/2,0,1/2)>=0,                        (13.9)
```

the active pin holds, and all punishment floors follow from zero own
singleton rewards.  With support owners `(a,b)=(1,3)` and outsiders
`(c,d)=(2,4)`,

```text
r_1(2)=-1<0<r_3(2)=2,
r_3(4)=-1<0<r_1(4)=2.                               (13.10)
```

Thus the packet is crossed and lies in both preemption alternatives for every
`0<g<=1`.  Completing the nonsingleton rows by (13.4), the common stationary
rate `1/2` is an exact terminal Nash profile with payoff zero.  This is an
exact rational packet-level instance of the four-dimensional open compiler
chamber, not merely an abstract toggle table.

### Corollary 13.3 (opposite support is forced in this chamber)

Within the constant-containing family (13.4), a support-two singleton packet
can use only an opposite pair `{1,3}` or `{2,4}`.  Indeed, every adjacent pair
in (13.1) contains one low-context relation

```text
r_j(i)=q_i-b_i<q_i=r_i(i),                           (13.11)
```

contradicting the mutual support inequalities (12.22).  For an opposite pair,
each label is neutral for the other, so both cross-singleton payoffs equal the
corresponding own payoff and the support inequalities are equalities.  Thus
the support placement used in Proposition 13.2 is not an arbitrary convenient
choice; it is the only placement compatible with the packet pin, up to cyclic
relabeling.

## 14. Exact five-shape classification of three-face six-cycles

The remaining six-cycle geometry is small enough to classify without a global
cube search.

### Proposition 14.1 (five relabeling orbits)

Up to player relabeling and cyclic rotation/reversal, an empty-base simple
six-cycle whose union has three players is exactly one of the following five
coalition patterns:

```text
(E23) empty-1-12-2-23-3-empty,
(E12) empty-1-12-123-13-3-empty,
(P12) empty-1-12-123-23-3-empty,
(P03) 1-12-2-23-3-13-1,
(E01) 1-12-2-23-123-13-1.                            (14.1)
```

Proof.  Work in the three-cube on the cycle's union.  A simple six-cycle omits
exactly two of its eight vertices.  The cube is bipartite with four even and
four odd vertices, while the cycle uses three vertices of each parity.
Therefore the two omitted vertices have opposite parity, so their Hamming
distance is odd: either one or three.

If their distance is one, the omitted pair is an edge.  Coordinate
permutations preserve cardinality, so there are three cases according as that
edge joins layers `0-1`, `1-2`, or `2-3`.  The four degree-two vertices in the
remaining graph force the Hamiltonian six-cycle, giving `(E01),(E12),(E23)`.

If the distance is three, the omitted vertices are antipodal.  There are two
cardinality types, `0-3` and `1-2`.  Every remaining vertex then has degree
two, so the remaining graph itself is the unique six-cycle, giving `(P03)` and
`(P12)`.  This proves exhaustiveness and inequivalence.

Pattern `(P03)` is the singleton-pair cycle compiled on an open chamber by
Propositions 12.3--12.4.  Pattern `(P12)` is the graph/Bellman separation used
in Proposition 12.2.  Thus, after the persistent-base compiler, the
three-dimensional six-cycle residual has exactly four further shape orbits to
analyze, not an unstructured family of walks.  This is only a geometric
collector: each shape still carries its own directed reward inequalities.

### Proposition 14.2 (every six-cycle shape has an open stationary chamber)

For each of the five patterns in (14.1), there is an exact rational
constant-containing reward table at which:

1. all six displayed toggle inequalities are strict;
2. the common interior rate `p_1=p_2=p_3=1/2` solves (12.2); and
3. the rate Jacobian is invertible.

Consequently every geometric six-cycle orbit—not only `(P03)`—contains a
nonempty Euclidean-open subchamber accepted by the stationary all-behavior
compiler.

Here is finite exact data.  Give active player `i` a constant Quit payoff
`q_i` on every active coalition containing it.  For a nonempty opponent
coalition `R`, write

```text
delta_i(R)=q_i-r_R(i).                               (14.2)
```

List the three deltas for players `1,2,3` in the orders
`(2,3,23)`, `(1,3,13)`, and `(1,2,12)` respectively:

```text
shape   player 1       player 2       player 3       det J
E23     (-4,-4, 8)     ( 1,-4, 3)     (-4, 1, 3)       68
E12     (-4,-4, 8)     ( 1, 1,-2)     (-4,-4, 8)      -32
P12     (-3, 4,-1)     ( 1,-4, 3)     (-4,-4, 8)       64
P03     (-4, 1, 3)     ( 1,-4, 3)     (-4, 1, 3)       63
E01     (-4,-4, 8)     ( 1, 1,-2)     (-4, 1, 3)      -12. (14.3)
```

For the three shapes containing `empty`, choose `q_1=1,q_3=-1`; player `1`
is the empty-edge joiner and player `3` the empty-edge leaver.  Take `q_2=0`.
For `(P03),(E01)`, take all `q_i=0`.

Proof.  Each row triple in (14.3) sums to zero.  At common rate `1/2`, the
three nonempty opponent coalitions all have probability `1/4`, so

```text
H_i=(delta_i(j)+delta_i(k)+delta_i(jk))/4=0.          (14.4)
```

Adding player `i` at context `R` has gain `delta_i(R)`; removing it has gain
`-delta_i(R)`.  Reading the signs against the five cycles verifies all six
strict arrows.  The empty-context arrows are exactly `q_1>0` and `q_3<0`.

If a player's singleton deltas are `(u,v)` and its pair delta is `-u-v`, its
Jacobian derivatives at the common rate are `(-v,-u)` in the two opponent
variables.  Substitution gives the five nonzero determinants displayed in
(14.3).  The implicit-function theorem and persistence of strict signs now
give an open stationary-solution neighborhood for each row.  A fourth passive
player can be made strictly content by paying it zero on active terminal
coalitions and `-1` whenever it joins; then `U_4=0>J_4=-1`.

This proposition proves availability of a checked compiler on an open part of
every six-cycle shape.  It does **not** say the cycle signs force the
stationary equations; Proposition 12.2 already disproves that stronger
claim, and arbitrary sign-compatible tables remain in the semialgebraic
residual of Proposition 12.1.

### Proposition 14.3 (universal cycle-pattern availability)

The availability statement extends to every directed empty-base cycle
pattern using at least three active coordinates.

> Let `C` be any directed simple toggle cycle on an active set `F`, with
> `|F|>=3`, empty intersection, and union `F`.  There is a reward table
> realizing every directed edge of `C` strictly and an interior stationary
> product root accepted by Proposition 12.1.  Moreover the construction can
> be chosen transverse, so a full Euclidean-open neighborhood of tables keeps
> the same strict cycle and a nearby stationary compiler input.

Proof.  Fix the candidate common rate `p_0=1/2`.  For each active player `i`,
give every coalition containing `i` the constant payoff `q_i`.  For every
nonempty opponent context `R subset F\{i}`, choose

```text
delta_i(R)=q_i-r_R(i).                               (14.5)
```

If `C` adds `i` at context `R`, require `delta_i(R)>0`; if it removes `i`,
require `delta_i(R)<0`.  A simple cycle never uses the same cube edge twice,
so these requirements do not conflict.  An edge at the empty context is
handled separately by choosing `q_i>0` for a join and `q_i<0` for a leave.

The nonempty-context signs can always be completed so that

```text
sum_(nonempty R subset F\{i}) delta_i(R)=0.          (14.6)
```

Indeed, if both join and leave contexts occur away from empty, scale their
positive and negative magnitudes to balance.  If only one sign occurs away
from empty, the opposite toggle is the unique empty-context edge.  Join and
leave toggles of one coordinate alternate around a cycle, so in this case
`i` is toggled exactly twice.  Because `|F\{i}|>=2`, there is then an unused
nonempty context to carry the balancing opposite sign.  Unconstrained entries
may be perturbed, so the solutions of
(14.6) satisfying all prescribed signs form a nonempty relatively open set.

At common rate `1/2`, all nonempty opponent contexts have equal probability.
Thus (14.6) is exactly `H_i=0`.  It remains to choose the deltas so the rate
Jacobian is invertible.  Write `k=|F|-1` and consider the linear map on the
hyperplane (14.6)

```text
L_i(delta)_j = sum_(R containing j) delta_i(R)
                 (j in F\{i}).                       (14.7)
```

This map is onto `R^k`.  Explicitly, given target coordinates `g_j`, use only
the singleton contexts and the full opponent context: set

```text
y=(sum_j g_j)/(k-1),
delta_i({j})=g_j-y,
delta_i(F\{i})=y.                                    (14.8)
```

Then the total sum is zero and (14.7) equals `g`.  At rate `1/2`, the gradient
row of `H_i` is a fixed positive scalar multiple of `L_i(delta)`.  Since a
surjective linear map sends the nonempty relatively open sign set above to an
open subset of the off-diagonal row space, the possible Jacobians contain a
nonempty open subset of all zero-diagonal matrices.

The determinant is not identically zero on that space: a cyclic permutation
matrix has zero diagonal and determinant `+/-1`.  Hence one may choose the
rows from the sign-compatible open sets so that the Jacobian is invertible.
The implicit-function theorem supplies the claimed open reward neighborhood.
Any inactive player is made strictly content by payoff zero when it stays out
and `-1` whenever it joins.  Proposition 12.1 then gives exact terminal Nash
against all behavioral deviations and a uniform payoff.

This is an **availability theorem for every finite cycle pattern**, not a
consumer of arbitrary strict-cycle data.  The reward magnitudes are selected
to solve the stationary equations; a given counterexample-witness table may
lie in the complementary semialgebraic residual.  Thus the theorem identifies
the stationary compiler as genuinely present in every geometric branch
without assuming away the remaining producer problem.

## 15. Semantic dispatch for the checked selected-toggle cycle

The checked reachable cycle can now be fed directly into the preceding
game-semantic tests.  This is the useful classification; no further cycle-
existence argument is needed.

Fix a four-player reward table, a
`QuittingTerminalExploitabilityWitness reward`, a crossed support-two packet,
and one supplied `witness.ReachableStrictToggleSimpleCycle seed` returned by
the checked finite residual.  Let `C=(S_0,...,S_{L-1})` be its cyclic vertex
list.  Thus every displayed edge changes one player, is a literal strict
reward-table toggle selected by the checked reachable successor, and
`4<=L<=16` is even.  Define

```text
B = intersection_k S_k,
F = (union_k S_k) \ B,
O = I \ (B union F).                                (15.1)
```

The simple cycle toggles at least two free coordinates, so `|F|>=2`; and
`B,F,O` are pairwise disjoint with union the full player set.

The following declarations were inspected for this handoff:

```text
nonempty_finFourCrossedSupportTwoFiniteResidual
  (Diagnostics/Quitting/Collision/SingletonPacket/FiniteFaceAggregate.lean),
ReachableStrictToggleSimpleCycle and
exists_reachableStrictToggleSimpleCycle
  (Diagnostics/Quitting/Collision/Toggles/ReachableSimpleCycle.lean),
quittingCollisionRepairWorks_iff and
quittingInstantPunishmentεEquilibriumExistence_of_collisionRepair
  (Quitting/Boundary/Repair/CollisionRepairCharacterization.lean;
   Quitting/Classification/ExistenceBranches.lean),
isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary
  (Quitting/Stationary/EndpointCompiler.lean),
quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter
  (Quitting/Classification/InstantPunishmentEquivalence.lean),
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  (Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean).
```

Sections 10--12 give ordinary-mathematics verifiers whose accepted profiles
feed these checked unrestricted-behavior consumers.  No claim is made that
the new finite case split itself is already a Lean declaration.

### Proposition 15.1 (cycle-to-semantic finite dispatch)

Exactly one of the following finite outputs may be returned, after testing in
the displayed order.

1. If `L=4`, apply the explicit face tests of Section 10.  A passing
   blocker/base/stationary test gives a checked all-behavior compiler input;
   otherwise return the corresponding finite failure disjunction (10.9),
   (10.10), or (10.19).
2. If `B` is nonempty, enumerate the at most `3^|F|<=27` support-status cells
   of the induced binary game in Proposition 11.1.  If one Nash solution
   passes its base-leave and outsider-join inequalities, return the
   sure-blocker/instant-punishment compiler input.  Otherwise return the exact
   residual

   ```text
   for every induced-game Nash x, G_(B,F)(x)>0,       (15.2)
   ```

   together with the fixed positive compact gap `gamma_(B,F)` from (11.7).
3. If `B` is empty, use `F` as the active set in (12.1)--(12.5).  An interior
   solution returns the exact stationary all-behavior compiler input.
   Otherwise return

   ```text
   no p in (0,1)^F satisfies all H_i(p)=0
     and all passive inequalities J_o(p)<=U_o(p).    (15.3)
   ```

Under the maintained terminal exploitability witness, every tested compiler
branch is impossible, so the checked cycle necessarily lands in the named
failure output of its case.

Proof.  Section 10 proves item 1, including unrestricted deviations.  Finite
Nash existence and Proposition 11.1 prove item 2; Corollary 11.2 supplies the
strict uniform gap when no Nash point passes.  Proposition 12.1 proves item 3.
All cases use the literal reward table and the actual punishment value; the
static cycle supplies only the finite label sets in (15.1), not a fabricated
chronology.

This is a relabeling-invariant finite semialgebraic reduction.  In item 2,
each Nash support cell is given by finitely many multilinear equalities and
weak inequalities, and `G>0` is another polynomial inequality after the
product weights are expanded (with the exact punishment value retained as the
supplied scalar input allowed by the question).  In item 3, multiplying passive inequalities by
the positive absorption denominator leaves only the explicit polynomials
(12.2)--(12.5).  Projection/negation preserves semialgebraicity; no infinite
strategy menu or bounded-controller completeness assumption is used.

The reduction is strict but not complete.  Conditions (15.2) and (15.3) are
the precise remaining cycle chambers for these existing compilers.  They do
not imply a periodic chronology, collision certificate, or uniform payoff.
The open examples in Sections 12--14 show that neither residual is forced by
cycle geometry alone.

For clarity, residual (15.2) is fully explicit.  Write `NE(B,F)` for the
nonempty compact mixed-Nash set of the induced binary game on `F`.  For
`x in NE(B,F)`, let `mu_x` be its product law and `V,J` be (11.2)--(11.3).
If `|B|>=2`, define `G_(B,F)(x)` as the maximum of

```text
J_o(x)-V_o(x)                                      (o in O),
sum_R mu_x(R) r_((B\{b}) union R)(b)-V_b(x)         (b in B). (15.2a)
```

If `B={b}`, replace the second line by

```text
sum_(nonempty R) mu_x(R) r_R(b)
  +mu_x(empty)*chi_b-V_b(x).                        (15.2b)
```

The maximum is over a nonempty finite family of deviation excesses.  A point
with `G<=0` is exactly the persistent-base compiler input of Proposition
11.1.  Under the terminal witness every `x in NE(B,F)` has `G(x)>0`, so
compactness gives the exact residual datum

```text
gamma_(B,F)=min_(x in NE(B,F)) G_(B,F)(x)>0.         (15.2c)
```

All terms are finite multilinear polynomials in the support-cell variables,
apart from the supplied scalar punishment value `chi_b`, which the maintained
question explicitly permits.  This is the precise nonempty-base chamber to
attack; “some Nash choice fails” is not being used as a substitute.

Residual (15.3) is equally literal.  For `p in (0,1)^F`, let `mu_-i` be the
product law of the opponents in `F\{i}` and set

```text
d_i(p)=sum_(nonempty R) mu_-i(R),
N_i(p)=sum_(nonempty R) mu_-i(R) r_R(i),
Q_i(p)=sum_R mu_-i(R) r_(R union {i})(i),
H_i(p)=d_i(p)Q_i(p)-N_i(p).                         (15.3a)
```

With `mu_p` the full product law, define

```text
delta(p)=sum_(nonempty R) mu_p(R),
U_k(p)=sum_(nonempty R) mu_p(R)r_R(k)/delta(p),
J_o(p)=sum_R mu_p(R)r_(R union {o})(o).             (15.3b)
```

The exact empty-base residual is

```text
not exists p in (0,1)^F,
  [forall i in F, H_i(p)=0]
  and [forall o in O, J_o(p)<=U_o(p)].              (15.3c)
```

Because `delta(p)>0`, clearing it from the passive inequalities makes (15.3c)
a finite polynomial/sign chamber.  A solution is exactly the input consumed
by the checked stationary endpoint theorem: every active player is indifferent,
every passive player prefers Continue, and at least two active hazards give
every player the deleted-clock contraction needed to cover all behavioral
stopping times and Never.  No root sequence is assumed in the negated branch.

### Corollary 15.2 (vanishing-defect stationary sequences escape to the boundary)

The no-solution residual (15.3) has a quantitative compact-interior form.  For
an active rate vector `p`, let

```text
A_o(p)=sum_(nonempty R subset F) mu_p(R) r_R(o),
P_o(p)=delta(p) J_o(p)-A_o(p),

W(p)=max( max_(i in F)|H_i(p)|,
          max_(o in O) max(P_o(p),0) ).               (15.4)
```

The passive maximum is read as zero when `O` is empty.  Here `P_o<=0` is
exactly the denominator-cleared passive inequality.  If
(15.3) holds, then for every `0<rho<1/2` there is a constant
`gamma_rho>0` such that

```text
W(p)>=gamma_rho       whenever rho<=p_i<=1-rho for all i.  (15.5)
```

Proof.  The box `[rho,1-rho]^F` is compact, `W` is continuous and
nonnegative, and `W(p)=0` is equivalent to all equations and passive
inequalities in (12.5).  Under (15.3) it is strictly positive everywhere on
the box, so its attained minimum is positive.

Consequently any sequence of stationary roots whose active Bellman/passive
defects tend to zero must approach a coordinate face:

```text
min_(i in F) min(p_i,1-p_i) -> 0                     (15.6)
```

and the sequence cannot remain in any fixed compact interior box.  Thus the
exact remaining empty-base obstruction is a **boundary escape**,
not an interior compactness failure.  No claim is made that the boundary
limit itself satisfies a blocker, collision, or lower-dimensional compiler;
identifying that limiting face is the next producer step.

The existence of such a sequence is an additional hypothesis, not a
consequence of the strict-toggle cycle or of (15.3).  Thus this corollary is a
boundary screen for a proposed stationary approximation, not a consumer of
the entire empty-base residual.

### Corollary 15.3 (terminal witnesses force a negative or all-Continue boundary)

The first boundary classification is nevertheless exact.  Let `p_n` be
interior active rate vectors with `W(p_n)->0`, and pass to a subsequence
`p_n->p_*`.  Under a terminal exploitability witness, write

```text
P_*={i in F : 0<p_*(i)}.
```

Then

```text
|P_*|<=1.                                             (15.7)
```

If `P_*={j}`, necessarily

```text
r_j(j)<0.                                             (15.8)
```

If `P_*` is empty, at least one player in the full player set has positive own
singleton reward.

Proof.  Suppose first that at least two active rates are positive at the
limit.  Every player's opponents then contract strictly.  Continuity sends
`W(p_n)->0` to all limiting equations `H_i(p_*)=0` and passive inequalities.
As in Proposition 12.1, these are the exact stationary endpoint Nash
conditions, so the limiting root is an exact terminal Nash profile against
all behavioral deviations.  Fixed-target selection contradicts the terminal
witness.  This proves (15.7).

If only `j` has positive rate, every other player still faces strict opponent
contraction and is controlled by the limiting equations.  Player `j`'s
opponents Continue surely; its stationary profile eventually terminates at
the singleton `{j}`, and its only additional full-rate alternative is Never,
with payoff zero.  If `r_j(j)>=0`, the exact stationary boundary condition
holds and the same endpoint compiler again gives an exact terminal Nash
profile.  Therefore the witness forces (15.8).

If all rates vanish, the limiting root is all-Continue.  When every own
singleton reward is nonpositive, all-Never is already an exact terminal Nash
profile: a unilateral player can only Quit alone or Never.  The witness
therefore forces some positive own singleton.

Thus every approximate stationary escape from the empty-base cycle screen
has only two terminal-witness limits: a unique negative-solo hazard carrier,
or the all-Continue face with a positive-solo escape.  This is a finite
boundary reduction, not yet a chronology.  In the support-two packet branch,
a supported unique carrier can occur only in the checked negative-owner
alternative; the preempted/nonnegative owner case cannot be that limit.

## 16. Next question

### Proposition 16.1 (a supported negative boundary carrier forces a join)

Let `j` belong to the positive support of the normalized singleton packet and
suppose `r_j(j)<0`.  Packet pinning and the punishment floor give

```text
chi_j <= target_j = r_j(j).                          (16.1)
```

If

```text
r_{i,j}(i) <= r_j(i)             for every i!=j,     (16.2)
```

then the root in which `j` Quits surely and everyone else Continues, followed
after all-Continue by an accuracy-dependent stationary near-minmax punishment
of `j`, is a terminal `epsilon`-Nash profile for every `epsilon>0`, with fixed
payoff vector `r_j`.  Hence `r_j` is a uniform-equilibrium payoff.

Proof.  Every spectator's arbitrary deviation reduces to its date-zero
Continue/join choice because `j` Quits surely; (16.2) is exactly no-join.  If
`j` follows the root it receives `r_j(j)`.  If it Continues, the all-Continue
branch reaches a punishment with unilateral cap at most `chi_j+epsilon`, which
is at most `r_j(j)+epsilon` by (16.1).  This is the checked instant-punishment
compiler, and nominal play absorbs at date zero with the fixed payoff `r_j`.

Therefore, under the terminal exploitability witness, every supported
negative carrier satisfies the strict finite alternative

```text
there exists i!=j with r_{i,j}(i)>r_j(i).            (16.3)
```

This turns the supported part of Corollary 15.3's unique-negative boundary
into a literal singleton join edge.  If the negative carrier is an outsider,
the packet gives only `chi_j<=target_j`, not `chi_j<=r_j(j)`; that case remains
an explicit boundary chamber rather than being silently punished.

### Proposition 16.2 (the all-Continue boundary also forces a join)

Under a terminal exploitability witness, every player `j` with
`r_j(j)>=0` has some spectator `i!=j` satisfying (16.3).  Otherwise the pure
singleton `{j}` meets all membership-toggle inequalities: its owner weakly
prefers staying to Never, and every outsider weakly prefers not joining.
The checked sure-exit-set compiler would make it an exact terminal Nash
profile.  In particular, the positive-solo label forced at the all-Continue
boundary of Corollary 15.3 always supplies a strict singleton join anchor.

Together, Propositions 16.1--16.2 reduce every stationary boundary limit to
one of two finite outputs:

```text
* a strict singleton join edge; or
* a unique negative carrier outside the packet support.             (16.4)
```

The first output is real strategic data but is not by itself a chronology;
the second is the genuinely new boundary chamber.

## 17. Crossed harm makes every outsider normal

The direct collision-premium analysis below is valid, but Proposition 17.3
subsequently supersedes it for the terminal-counterexample dispatch: crossed
harm already proves punishment normality without a pair-payoff hypothesis.

### Proposition 17.1 (crossed-owner punishment)

Let `x` be an outsider with `r_x(x)<0`, and let `h` be a supported owner which
harms it at the singleton row:

```text
r_h(x)<r_x(x).                                       (17.1)
```

Assume the sure-`x` root has no profitable spectator join,

```text
r_{i,x}(i)<=r_x(i)                 for every i!=x,   (17.2)
```

and that `x` does not gain by joining the punishment owner,

```text
r_{h,x}(x)<=r_x(x).                                  (17.3)
```

Then `r_x` is a uniform-equilibrium payoff.

Proof.  Use the first root in which `x` Quits surely and every other player
Continues.  If `x` Continues, switch to the stationary punishment row in
which `h` Quits surely.  Against that row, `x`'s unrestricted unilateral cap
is exactly

```text
max(r_h(x),r_{h,x}(x)) <= r_x(x)                     (17.4)
```

by (17.1),(17.3): Continue yields `{h}`, Quit yields `{h,x}`, and absorption
is immediate.  Every other player is controlled at the first row by (17.2),
because nominal `x` Quits surely.  Thus this is an exact instance of the
instant-punishment compiler, with fixed nominal payoff `r_x`.

Under a terminal witness, either a singleton spectator join (16.3) already
exists or (17.3) must fail strictly:

```text
r_{h,x}(x)>r_x(x).                                   (17.5)
```

In the crossed support notation, outsider `c` is harmed by supported owner
`a`, and outsider `d` by supported owner `b`.  Hence the unique negative-
outsider boundary of Corollary 15.3 returns one of the finite outputs

```text
some i joins {c},  or  r_{a,c}(c)>r_c(c),
some i joins {d},  or  r_{b,d}(d)>r_d(d),            (17.6)
```

according to the carrier label.  The second alternative is a literal
positive collision premium for the harmed outsider, not another compactness
statement.

### Corollary 17.2 (the premium purifies a new collision orientation)

On the no-join residual, (17.1) and (17.5) give the strict sandwich

```text
r_h(x)<r_x(x)<r_{h,x}(x).                            (17.7)
```

For the collision-repair orientation with owner `x` and sure blocker `h`, the
owner endpoints are `r_h(x)` and `r_{h,x}(x)`.  Thus owner optimality purifies
the owner rate to `1`.  Testing the two remaining rate-one
`QuittingCollisionSpectatorNoJoin` and `QuittingCollisionBlockerBalance`
predicates now gives a finite output:

```text
* the checked rate-one collision-repair compiler input; or
* an explicit failed spectator/blocker predicate at orientation (x,h). (17.8)
```

At rate one those two predicates simplify completely:

```text
r_x(h) <= r_{x,h}(h),
r_{x,h,s}(s) <= r_{x,h}(s)       for every s notin {x,h}.  (17.9)
```

The punishment value disappears.  Together with the owner's strict retention
from (17.7), these are exactly the sure-exit inequalities for the pair
`{x,h}`.  Hence, under the terminal witness, failure is one of the literal
anchored toggles

```text
r_x(h)>r_{x,h}(h),
or
r_{x,h,s}(s)>r_{x,h}(s)          for some s notin {x,h}.  (17.10)
```

The first makes blocker `h` leave the pair; the second makes a spectator join
it.  Thus the boundary carrier label `x` and harmed owner `h` are retained in
the next finite state.

This use of collision repair is legal even though `x` is outside the original
packet support: the repair characterization itself is a reward-table/root
verifier.  What does **not** automatically transfer is the packet-specific
theorem which manufactures a positive spectator defect after a supported-
owner failure.  Therefore (17.8), rather than an unproved new join, is the
honest final chamber.

Combining Sections 15--17, every approximate-stationary escape from an
empty-base checked cycle now yields either a checked compiler or a strict
singleton/pair reward defect with named crossed labels.  Turning that defect
into a compatible nonstationary chronology remains open.

### Proposition 17.3 (crossed harm eliminates the negative no-join boundary)

Declarations inspected for this step:

```text
abnormal_singletonFloor_chain
  (Quitting/Classification/AbnormalSingletonConsequences.lean),
isQuittingNormalPlayer_of_mass_pos
  (Quitting/Classification/SingletonPacketSupport.lean),
exists_punishRow_stationaryUnilateralCap_le
  (Quitting/Classification/ExistenceBranches.lean),
not_quittingInstantPunishmentεEquilibriumExistence
  (Quitting/Classification/TerminalExploitabilityBranchExclusions.lean),
isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin
  (Quitting/Paths/AnchoredJoinPromotion.lean).
```

In fact, the collision-premium branch above is unnecessary for the terminal
counterexample reduction.  Suppose only that

```text
r_h(x)<r_x(x),                                      (17.11)
r_{i,x}(i)<=r_x(i)                  for every i!=x. (17.12)
```

Then the game has the instant-punishment branch, with `x` as the sure first
quitter and target payoff `r_x`.  Consequently a terminal exploitability
witness forces a strict singleton join at `x`.

Proof.  Player `x` cannot be punishment-abnormal.  Indeed, if
`r_x(x)<chi_x`, the checked abnormal singleton-floor theorem
`abnormal_singletonFloor_chain` applied to the different owner `h` gives

```text
r_x(x)<chi_x<=r_h(x),                               (17.13)
```

contradicting (17.11).  By linear order, `x` is therefore punishment-normal:

```text
chi_x<=r_x(x).                                      (17.14)
```

For every `epsilon>0`, choose the checked accuracy-dependent stationary
punishment row whose unrestricted unilateral cap for `x` is at most
`chi_x+epsilon`.  At the first row let `x` Quit surely and every other player
Continue.  Player `x` obtains `r_x(x)` and cannot gain more than `epsilon` by
Continuing into the punishment.  Every other player's arbitrary behavioral
deviation reduces to its first-row Quit/Continue choice because `x` Quits
surely; (17.12) says joining cannot improve its payoff.  Hence this is a
terminal `epsilon`-Nash profile for every positive accuracy, with nominal
payoff `r_x`.  This is exactly the checked instant-punishment interface and
is excluded by `not_quittingInstantPunishmentεEquilibriumExistence` under a
terminal exploitability witness.

Applied to the crossed packet, `h=a,x=c` or `h=b,x=d` already supplies
(17.11).  Thus the negative-outsider alternative of Corollary 15.3 cannot
survive together with singleton no-join.  Combining with Proposition 16.2,
every boundary escape in Corollary 15.3 returns

```text
there exist x and i!=x with r_{i,x}(i)>r_x(i).       (17.15)
```

This is a literal strict singleton join and is accepted by the checked
anchored-join promotion step.  That step may expose a further strict toggle
rather than a compiler, so (17.15) is a strict reduction of the stationary
boundary, not a closure of the full selected-toggle cycle.

### Corollary 17.4 (both crossed outsiders are fixed normal join anchors)

The same argument is independent of the stationary boundary.  In the crossed
packet notation,

```text
r_a(c)<r_c(c),             r_b(d)<r_d(d).           (17.16)
```

Therefore both outsiders `c,d` are punishment-normal.  The packet theorem
`isQuittingNormalPlayer_of_mass_pos` also makes both supported owners `a,b`
punishment-normal.  Under a terminal exploitability witness, **every** player
must consequently have a strict singleton join:

```text
for every x in {a,b,c,d},
there is i!=x with r_{i,x}(i)>r_x(i).               (17.17)
```

Proof.  Apply the abnormal-floor contradiction in Proposition 17.3 first to
`(h,x)=(a,c)` and then to `(b,d)`.  Combine the resulting outsider normality
with support normality.  If any one of the four singleton rows had no strict
join, its normal sure quitter and near-minmax continuation would give the
excluded instant-punishment branch.

Thus the final crossed chamber carries four singleton-anchored strict toggles
before any collision orientation or stationary-rate limit is chosen.
Applying `isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin` to each one
either returns a checked sure-exit input or extends it by an old-member leave
or another outsider join without immediately undoing the entering player.
This is stronger label information than an unspecified positive join, but it
still does not force the two promoted paths to meet or form a compiler-accepted
cycle.

There is also a useful principal-matrix consequence.  Since all four players
are punishment-normal,

```text
punishmentNormalPlayers(reward)=I.                  (17.18)
```

In this crossed support-two chamber, the punishment-normal principal matrix
is therefore the full ambient normalized singleton matrix.  Any hard
nonprojective principal returned by the checked LCP gate can be analyzed
directly with the exclusions in (1.4), without a hidden subtype/reindexing
loss.  This does not force such a principal to have size two and does not
decode its size-three or size-four cases.

This corollary is useful packet-level structure, but it is **not counted as a
new answer to the maintained selected-cycle subproblem**.  The question
already has checked join promotion and cycle collection.  To become a further
cycle reduction, the four anchors would have to be intersected with the
specific selected cycle's pair/triple reward cells or fed to a named
all-behavior compiler; neither implication is proved here.

## 18. Next question

### Proposition 18.1 (persistent-base gap localizes to a transverse pure toggle)

Take the genuine persistent-base residual A.2 of Proposition 15.1, and choose
an induced-game Nash point `x_*` minimizing `G_(B,F)`.  Thus

```text
G_(B,F)(x_*)=gamma_(B,F)>0.                          (18.1)
```

Then at least one of the following finite outputs holds:

```text
(join)  there are o in O and R subset F such that
        r_(B union R union {o})(o)-r_(B union R)(o)>=gamma_(B,F);

(leave) there are b in B and R subset F such that
        r_((B\{b}) union R)(b)-r_(B union R)(b)>=gamma_(B,F);

(floor) B={b} and chi_b-r_b(b)>=gamma_(B,F).         (18.2)
```

The first two are literal strict toggles transverse to the selected cycle's
face: the join inserts a player from `O`, while the leave removes a player
from the persistent base `B`.  The third is possible only for a singleton
base.

Proof.  One of the finitely many expressions defining `G(x_*)` is at least
`gamma`.  An outsider expression is the product-law expectation of the pure
join gains

```text
r_(B union R union {o})(o)-r_(B union R)(o).
```

An `|B|>=2` base expression is the expectation of the displayed pure leave
gains.  A singleton-base expression is the expectation, over
`R subset F`, of the same leave gain for `R nonempty`, with the empty-cell
gain defined to be `chi_b-r_b(b)`.  A convex average cannot exceed every one
of its summands, so one summand is at least `gamma`.  This gives (18.2).

In the crossed support-two packet the floor output is impossible.  The two
positive-mass support owners are punishment-normal by
`isQuittingNormalPlayer_of_mass_pos`.  Each outsider is also normal: the
crossed singleton row strictly below its own singleton would contradict
`abnormal_singletonFloor_chain` if it were abnormal.  Hence every player,
and in particular the singleton base owner, satisfies

```text
chi_b<=r_b(b).                                      (18.3)
```

Therefore A.2 splits, in the maintained chamber, into the two exact
relabeling-invariant transverse-toggle cases `(join)` and `(leave)`.

This is a genuine reduction of A.2: it uses its uniform compact gap and does
not assume a vanishing-defect stationary sequence.  It still does not compile
the transverse toggle.  The next step is to test its target coalition for the
checked sure-exit inequalities and, on failure, retain the resulting finite
pair/triple leave/join cell rather than invoking another abstract cycle
collector.

### Proposition 18.2 (one-step transverse promotion without immediate undo)

Let `S` be the source coalition and `T` the target of the quantitative toggle
from Proposition 18.1.

If the toggle is an outsider join, so `T=S union {o}` and

```text
r_T(o)-r_S(o)>=gamma>0,                             (18.4)
```

then exactly the checked anchored-join alternative holds:

```text
* T is a sure-exit set; or
* some old member m in S strictly prefers T\{m}; or
* some outsider j notin T strictly prefers T union {j}. (18.5)
```

The joining player `o` cannot be the leaving witness because (18.4) has the
opposite strict sign.

If the toggle is a base leave, so `S=T union {b}`, `T` is nonempty, and

```text
r_T(b)-r_S(b)>=gamma>0,                             (18.6)
```

then the symmetric finite alternative is

```text
* T is a sure-exit set; or
* some member m in T strictly prefers T\{m}; or
* some outsider j notin T, with j!=b, strictly prefers T union {j}. (18.7)
```

Proof.  A nonempty coalition is a sure-exit set exactly when every member
weakly prefers staying and every outsider weakly prefers not joining.  Negate
those finitely many inequalities.  In the join case, removing `o` returns
`S`, so (18.4) excludes `o` as a leaving witness; this is
`isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin`.  In the leave case,
rejoining `b` returns `S`, so (18.6) excludes `b` as the outsider joining
witness.  All other failures are precisely (18.7).

Under the terminal exploitability witness the sure-exit output is impossible,
because its pure date-zero root is an exact terminal Nash profile against all
behavioral deviations.  Thus A.2 now returns a length-two anchored toggle
path with its first transverse edge still carrying the fixed gap `gamma`, and
with no immediate reversal of the player responsible for that edge.

This is a finite nonsingleton reward-table reduction, not another cycle
existence theorem.  Pair, triple, and possibly grand-coalition cells may
occur.  It makes no quantitative claim about the second strict edge and does
not yet feed the two-edge path to a chronology compiler.

## 19. Next question

### Proposition 19.1 (the genuine post-four-cycle A.2 arm has only a base leave)

In the ordered dispatch of Proposition 15.1, a genuine A.2 residual has
already failed the `L=4` branch.  Consequently, in the four-player problem,

```text
B={b},                 |F|=3,                 O=empty,
L in {6,8}.                                                   (19.1)
```

Moreover Proposition 18.1 necessarily returns a nonempty `R subset F` with

```text
r_R(b)-r_(R union {b})(b)>=gamma_(B,F)>0.            (19.2)
```

There is no outsider-join arm and no floor arm.

Proof.  A simple cube cycle uses at least two free coordinates.  If it used
exactly two, its face would have four vertices and the simple cycle would
have length four, already handled by the first ordered branch.  Hence
`|F|>=3`.  Since `B` is nonempty and there are only four players, equality is
forced: `|F|=3`, `|B|=1`, and `O` is empty.  The cycle is then a non-four
even simple cycle in a three-cube, so its length is six or eight.

With `O=empty`, the sole expression in `G_(B,F)` is the singleton-base leave
expression (15.2b).  Its empty-cell summand is
`chi_b-r_b(b)<=0` by punishment normality, while its value at the minimizing
Nash point is `gamma_(B,F)>0`.  Therefore some positive-weight nonempty cell
`R` has pure leave gain at least `gamma_(B,F)`, which is (19.2).

Thus the maintained A.2 arm is not a generic join/leave disjunction.  It is a
quantitative departure of the unique persistent base player from one
nonempty cell of the three-free-player face.

### Proposition 19.2 (exact incidence split and matching-pennies square)

Put

```text
S=R union {b},             T=R.
```

Apply Proposition 18.2 to (19.2).  Under the terminal witness the sure-exit
arm is excluded, so choose one returned strict second edge.  That edge toggles
a unique coordinate `i in F`, and there is a coalition

```text
U=T triangle {i}
```

such that the strict second edge is `T -> U`.  Set

```text
V=S triangle {i}=U union {b}.                         (19.3)
```

The following finite, relabeling-invariant alternatives are exhaustive.

1. `S` is not a vertex of the selected cycle.  Return the **off-cycle pure
   cell** `(R,b,i)` together with the gap (19.2) and the strict edge `T->U`.
2. `S` is a cycle vertex but `V` is not one of its two cycle neighbors.
   Return the **nonincident-coordinate cell** with the same labelled data.
3. `V` is a cycle neighbor and the selected edge is oriented `S->V`.  Return
   the **outgoing-incidence cell**.
4. `V` is a cycle neighbor, its selected edge is oriented `V->S`, and

   ```text
   r_V(b)>r_U(b).                                      (19.4)
   ```

   Then there is an anchored strict four-cycle

   ```text
   S -> T -> U -> V -> S.                              (19.5)
   ```

   Its first edge retains the fixed gap `gamma_(B,F)`.  It is therefore fed
   directly to the complete length-four semantic dispatch of Section 10,
   which returns either a named all-behavior compiler input or one of the
   exact residuals (10.9), (10.10), or (10.19).
5. `V` is an incoming cycle neighbor as in item 4, but

   ```text
   r_V(b)<=r_U(b).                                     (19.6)
   ```

   At `U`, both `b` and `i` are stable against their membership toggles.  If
   the pure terminal action at `U` is not already an exact equilibrium, a
   third label

   ```text
   k in F\{i}
   ```

   supplies a strict toggle from `U`.  Thus this arm returns a three-edge
   path whose successive responsible labels are the three distinct players
   `b,i,k`, while its first edge still has gap `gamma_(B,F)`.

Proof.  Proposition 18.2 says the second witness is either an old member of
`R` leaving or a player of `F\R` joining; the excluded rejoining label is
`b`.  Hence in both cases it toggles exactly one `i in F`, giving (19.3).
Membership in a finite cycle, adjacency, its directed orientation, and the
sign in (19.4) are finite reward-table tests, so items 1--5 are exhaustive.

In item 4, (19.2) is `S->T`, promotion gives `T->U`, (19.4) is `U->V`, and
the incoming selected edge is `V->S`.  The four vertices are distinct
because `b!=i`; this proves (19.5).  Since `S` lies on the checked anchored
reachable cycle, the new four-cycle is reached at `S` and can use the
Section 10 dispatch without a new reachability assumption.

For item 5, the strict edge `T->U` says player `i` does not gain by reversing
its action at `U`; (19.6) says the absent player `b` does not gain by joining
`U`.  If `U` is nonempty, failure of the sure-exit membership inequalities
must therefore be caused by a player outside `{b,i}`.  If `U` is empty, the
same conclusion follows from the all-Never test: `b` and `i` have
nonpositive singleton gains, so any profitable singleton Quit belongs to a
third player.  Since `I={b} union F`, that player lies in `F\{i}`.

This proposition is not a general cycle compiler.  It strictly partitions
the live A.2 chamber into three explicit positional residuals, a returned
length-four compiler problem, and a distinct-label three-edge residual.  In
particular it does not discard the quantitative transverse edge by invoking
another unstructured cycle collector.

## 20. Next question

### Proposition 20.1 (every incident square is compiled or has a stable
two-coordinate corner)

Assume `S` is a selected-cycle vertex and `V=S triangle {i}` is one of its
two cycle neighbors.  Retain the strict transverse edges

```text
S -> T -> U,
```

where `S=T union {b}`, `V=U union {b}`, and `U=T triangle {i}`.  Then exactly
one of the following outputs is available.

1. The selected edge is incoming `V->S` and `b` strictly prefers to rejoin
   at `U`, namely `r_V(b)>r_U(b)`.  This is the anchored strict four-cycle
   (19.5), so the Section 10 dispatcher applies.
2. One of `U,V` is a pure Nash corner of the two-coordinate membership game
   of `{b,i}`, with the other two players' membership held fixed.  Under the
   terminal witness, a strict membership toggle at that corner is therefore
   supplied by one of the two remaining labels in `I\{b,i}`.

More explicitly, the stable corner in item 2 may be chosen by the finite
rule

```text
if r_V(b)<=r_U(b), choose U;
if r_V(b)> r_U(b) and the selected edge is S->V, choose V. (20.1)
```

Proof.  The edge `S->T` says that `b` prefers its absent action at the
`i`-state represented by `T`.  The edge `T->U` says that `i` strictly prefers
its action at `U` to the opposite action at `T`.

If `r_V(b)<=r_U(b)`, then at `U` player `b` weakly prefers to remain absent,
and player `i` strictly prefers its current action by `T->U`.  Thus `U` is a
pure Nash corner of the `{b,i}` face.

Suppose instead that `r_V(b)>r_U(b)`.  Then `b` strictly prefers its present
action at `V`.  If the selected edge is outgoing `S->V`, player `i` also
strictly prefers its action at `V`, so `V` is a pure Nash corner.  If the
selected edge is incoming `V->S`, the four strict arrows are exactly

```text
S -> T -> U -> V -> S,
```

which is item 1.  These cases exhaust the two possible orientations and the
weak/strict `b` comparison.

At the stable corner, neither `b` nor `i` can violate the pure terminal
membership inequalities.  If the corner is nonempty and is not a sure-exit
set, a different player supplies the strict leave/join witness.  If it is
empty, failure of all-Never similarly gives a positive singleton Quit by a
different player.  Thus the new toggler belongs to `I\{b,i}`.  This covers
unrestricted behavioral deviations only in the accepted four-cycle or pure
terminal branches; the returned third-label toggle is static data, not yet a
chronology.

This disposes of the outgoing-incidence cell of Proposition 19.2 and folds
the incoming cells into one exact dichotomy.  The only positional cases not
meeting this local square are now:

```text
S is off the selected cycle,  or
S is on the cycle but the coordinate i is nonincident there.       (20.2)
```

### Proposition 20.2 (finite geometry of the two nonincident residuals)

The residual (20.2) has the following exact cube-geometric refinement.

* If `L=8`, every face vertex lies on the selected Hamiltonian cycle.  Hence
  the off-cycle arm is empty, and a nonincident coordinate is a chord from
  `S` to another cycle vertex.
* If `L=6`, the two omitted vertices of the three-cube are either adjacent or
  antipodal.  Thus an off-cycle `S` either has one omitted neighbor (the
  adjacent-complement case) or all three of its neighbors lie on the cycle
  (the antipodal-complement case).  A nonincident edge from an on-cycle `S`
  ends either at an omitted vertex or at a nonneighboring cycle vertex.

Proof.  The length-eight statement is immediate because the three-cube has
eight vertices.  For length six, let the omitted vertices be `x,y`.  They
cannot have Hamming distance two.  Indeed their two common cube neighbors
are adjacent to both omitted vertices, so each has only one neighbor left in
the remaining induced subgraph.  It therefore cannot lie on a six-cycle,
whose vertices require two retained cycle neighbors.  Hence the omitted
distance is one or three.  The stated adjacency alternatives then follow by
toggling one coordinate.

This is only a finite positional refinement.  In particular a cube chord is
not a Bellman edge and the complement classification is not itself compiler
data.

## 21. Next question

### Proposition 21.1 (a rejoining nonincident chord gives a shorter-or-equal
semantic cycle with migrated base)

Assume the nonincident-coordinate residual of Proposition 19.2 with both
`S` and `V=S triangle {i}` on the selected cycle.  Thus `S,V` are cube
neighbors but not cycle neighbors.  Then:

1. if `r_V(b)<=r_U(b)`, the corner `U` is stable for the two-coordinate
   `{b,i}` membership game, and the terminal witness returns a strict toggle
   by one of the other two labels;
2. if `r_V(b)>r_U(b)`, let `P` be the directed selected-cycle arc from `V`
   to `S`.  The concatenation

   ```text
   S -> T -> U -> V  followed by P from V to S       (21.1)
   ```

   is an anchored simple strict cycle `C'` retaining the gap
   `gamma_(B,F)` on `S->T`.

In item 2, if the original cycle has length six, `C'` has length six.  If the
original has length eight, `C'` has length six or eight.  Moreover

```text
b notin intersection(C'),       i notin intersection(C').  (21.2)
```

Therefore the exact semantic dispatch of Proposition 15.1 applied to `C'`
returns one of:

```text
* an existing all-behavior compiler input;
* the empty-base polynomial residual B.2;
* a persistent-base residual A.2 whose unique base label
  k lies in F\{i}, hence k!=b.                         (21.3)
```

Thus a chord which re-enters the selected face cannot reproduce A.2 with the
same persistent base: it either reaches the empty-base chamber or migrates
the base to one of the two unused labels.

Proof.  The first item uses only `T->U` and the weak nonrejoin inequality:
player `i` is strict at `U`, while player `b` is weakly stable absent.  The
same pure-corner argument as Proposition 20.1 supplies the remaining-label
toggle if the full terminal test fails.

For item 2, `r_V(b)>r_U(b)` is the strict edge `U->V`.  The three-edge path
`S->T->U->V` is disjoint from the interior of `P`: its two internal vertices
omit `b`, whereas every selected-cycle vertex contains `b`.  The selected
arc is simple, and all four displayed vertices are distinct, so (21.1) is a
simple directed strict cycle reached from the original anchor through `S`.

Because `S,V` differ in one cube coordinate, the two selected-cycle arcs
between them have odd lengths.  Nonincidence excludes length one.  For a
six-cycle both arcs therefore have length three, so `C'` has `3+3=6` edges.
For an eight-cycle their lengths are three and five, giving six or eight
edges after the three-edge splice.

The vertices `S,T` differ in `b`, and `T,U` differ in `i`, proving (21.2).
If `C'` has nonempty intersection, it cannot contain both remaining labels:
otherwise only `b,i` would vary and the face would have four vertices, while
`C'` has length at least six.  Hence its persistent base is a singleton among
the two labels in `F\{i}`.  Proposition 15.1 is applicable literally to the
new anchored cycle and gives (21.3).  This use is not a generic recollection:
the splice has bounded length, carries the original fixed-gap edge, and
strictly excludes the old base from every returned persistent-base arm.

### Corollary 21.2 (only three positional arms remain)

After Propositions 20.1 and 21.1, the genuine A.2 positional obstruction has
only the following exact forms:

```text
(a) an off-cycle source S in a six-cycle face;
(b) a stable {b,i} face corner (from an incident non-cycle arm or a
    nonrejoining chord), followed by a strict toggle from a remaining label;
(c) a rejoining chord whose spliced semantic dispatch returns B.2
    or returns A.2 with a different persistent base;
(d) in a six-cycle, an on-cycle S whose nonincident neighbor V is
    one of the two omitted vertices, with a strict b-rejoin.         (21.4)
```

Compiler outputs and the stable terminal corners have been removed.  Item (d)
is distinct from the off-cycle-source arm: here `S` is on the cycle but `V`
is not, so Proposition 21.1 has no directed arc starting at `V`.  This is a
strict finite refinement, not a termination proof: repeated base migration
could revisit an earlier label, and no monotone potential is asserted.

## 22. Next question

### Proposition 22.1 (positional-free two-coordinate square completion)

The positional split is in fact unnecessary for the local semantic handoff.
Keep the four coalitions

```text
S=T union {b},        U=T triangle {i},        V=U union {b},
```

and the strict edges

```text
S -> T -> U,                                           (22.1)
```

where `S->T` retains the gap `gamma_(B,F)`.  No assumption is made that any
of `S,T,U,V` lies on the selected cycle.  Exactly one of the following
finite outputs holds.

1. If

   ```text
   r_U(b)>=r_V(b),                                      (22.2)
   ```

   then `U` is a pure Nash corner of the `{b,i}` membership face.
2. If `r_V(b)>r_U(b)` and

   ```text
   r_V(i)>=r_S(i),                                      (22.3)
   ```

   then `V` is a pure Nash corner of that face.
3. If `r_V(b)>r_U(b)` and `r_S(i)>r_V(i)`, then

   ```text
   S -> T -> U -> V -> S                               (22.4)
   ```

   is a strict matching-pennies four-cycle retaining the original gap on
   its first edge.  It is passed directly to the complete Section 10
   semantic dispatcher.

Proof.  At `U`, player `i` is strictly stable because reversing its action
returns `T`, while (22.2) makes the absent player `b` weakly stable.  This is
item 1.  In the complementary strict case, `b` is stable present at `V`.
Condition (22.3) also makes `i` stable at `V`, giving item 2.  If (22.3)
fails, the missing comparisons are the strict edges `U->V` and `V->S`, which
complete (22.4).  The weak/strict alternatives are exhaustive.

The four-cycle dispatcher is a reward-table semantic test and does not need
the square to have been an edge square of the original selected cycle.  Its
accepted branches still verify all unrestricted behavioral deviations; its
failed branches return only the explicit Section 10 semialgebraic residuals.

If item 1 or 2 occurs, test the corresponding pure coalition `P=U` or `P=V`
against all membership deviations.  Under the terminal witness it cannot be
a full pure terminal equilibrium.  Since `b` and `i` already pass their
tests, a strict toggle is supplied by one of the two labels in

```text
I\{b,i}.                                               (22.5)
```

For `P=empty`, this is the same all-Never argument: `b` and `i` have
nonpositive singleton gains, so a positive singleton belongs to a remaining
label.

### Corollary 22.2 (the positional A.2 residual is eliminated)

Propositions 19--22 reduce the genuine persistent-base residual A.2 to the
following exact finite outputs, with no remaining on-cycle/off-cycle/chord
qualification:

```text
* a strict four-cycle carrying the gamma_(B,F)-paid base-leave edge,
  followed by the Section 10 compiler/residual dispatch; or
* a pure coalition P stable against the two coordinates {b,i},
  together with a strict destabilizing toggle by k in I\{b,i}.       (22.6)
```

The path reaching `P` has length two when `P=U` and length three when `P=V`;
the fixed-gap edge is never discarded.  The second arm is a strictly smaller
semialgebraic chamber: two named membership inequalities are already solved
at one literal coalition, and only the two complementary labels may break
the terminal test.

Propositions 20.2 and 21.1 remain valid refinements if the original cycle
incidence is useful downstream, but they are no longer needed to exhaust the
A.2 positions.  This result still does not compile the stable-corner arm or
turn its third-label toggle into a chronology.

## 23. Next question

### Proposition 23.1 (stable-corner exchange square)

Let `P` be the stable corner returned in (22.6).  Among its two certified
stable labels `{b,i}`, at least one is strictly stable; call it `a`.  Let
`s` be the other stable label, and let `k in I\{a,s}` be a strict terminal
destabilizer of `P`.  Thus, with the empty-coalition payoff interpreted as
zero,

```text
r_P(a)>r_(P triangle {a})(a),
r_(P triangle {k})(k)>r_P(k).                        (23.1)
```

Put

```text
Q=P triangle {k},
R=P triangle {a},
W=P triangle {a,k}.                                  (23.2)
```

Then one of the following exact finite outputs holds.

1. `Q` is a pure Nash corner of the `{a,k}` membership face;
2. `W` is a pure Nash corner of that face;
3. the four coalitions form a strict cycle

   ```text
   P -> Q -> W -> R -> P,                             (23.3)
   ```

   which is sent to the Section 10 semantic dispatcher.

In items 1--2, one of the two stable coordinates is strict.  Therefore, if
the returned corner is not a full pure terminal equilibrium, its next strict
destabilizer belongs to the complementary pair of labels and the same lemma
can be invoked again without weakening all stable inequalities to equality.

Proof.  The strict edge `P->Q` makes `k` stable at `Q`.  Test player `a` at
that corner.  If

```text
r_Q(a)>=r_W(a),                                      (23.4)
```

then `Q` is stable for both `a,k`, with `k` strict, giving item 1.  Otherwise
`Q->W` is strict, so `a` is strict at `W`.  Test `k` there.  If

```text
r_W(k)>=r_R(k),                                      (23.5)
```

then `W` is stable for both labels, giving item 2.  If (23.5) fails, the
strict edges are `W->R` and, by (23.1), `R->P`; together with `P->Q->W`
they give (23.3).  All weak equality faces land in a pure-corner arm.

For the corner supplied by Proposition 22.1, strict stability is automatic:
at `U`, label `i` is strict because `T->U`; at `V`, label `b` is strict
because `U->V`.  Hence (23.1) introduces no new genericity assumption.

### Corollary 23.2 (exact stable-pair residual)

If the Section 10 and pure-terminal branches keep failing, A.2 returns a
finite **stable-pair exchange** step

```text
(P; {a,s}, strict a)  --->  (P'; {a,k}, one strict), (23.6)
```

where `k` was a destabilizer outside the old pair.  The inherited path from
the original A.2 source to `P` still contains the
`gamma_(B,F)`-paid base-leave edge.  This is more structured than a generic
toggle: each node certifies two membership inequalities at one literal
coalition, each transition exchanges exactly one stable label, and every
failed exchange square has already been passed through the four-cycle
dispatcher.

This corollary does not assert termination of repeated exchanges.  A repeated
stable pair at a different coalition is not an equilibrium, and a directed
cycle in the finite state space of `(coalition, stable pair)` is not by itself
a checked quitting compiler.

## 24. Next question

### Proposition 24.1 (exact crossed-packet boundary with no pure sink and no
directed square)

Stable-pair exchange cannot be closed from membership-edge orientation alone,
even inside exact crossed support-two packet data and the algebraic A.2
chamber.  Let the players be `0,1,2,3`, and define the rational reward table
below; unlisted `Never` payoffs are zero.

```text
S             r_S
{0}           (  1,  1,  0,  2)
{1}           (  1,  1,  2,  0)
{0,1}         (  2,  2,  0,  0)
{2}           (  0,  0,  1,  0)
{0,2}         (  1,  0, -1,  0)
{1,2}         (  0,  1,  1,  0)
{0,1,2}       (  1,  1,  1,  0)
{3}           (  0,  0,  0,  1)
{0,3}         (  1,  0,  0,  1)
{1,3}         (  0, -1,  0,  1)
{0,1,3}       (-10, -1,  0, -1)
{2,3}         (  0,  0, -1,  1)
{0,2,3}       (  1,  0, -1,  1)
{1,2,3}       (  0,  1, -1,  1)
{0,1,2,3}     (-10, -1,  1,  1).                    (24.1)
```

Take singleton mass `1/2` on each of `{0},{1}` and target

```text
v=(1,1,1,1).                                         (24.2)
```

These are literal normalized singleton-packet fields: (24.2) is the exact
singleton mixture, both supported coordinates are pinned, every solo payoff
is one, and every punishment value is at most one by choosing all opponents
to Continue.  The crossed inequalities are

```text
r_0(2)=0 < r_2(2)=1 < r_1(2)=2,
r_1(3)=0 < r_3(3)=1 < r_0(3)=2.                     (24.3)
```

The quantitative preemption screen also holds algebraically with `g=1`:

```text
r_0(2)+1=r_2(2),             r_1(3)+1=r_3(3).       (24.3a)
```

The persistent-base face `B={0}`, `F={1,2,3}` contains the strict six-cycle

```text
{0}->{0,1}->{0,1,2}->{0,1,2,3}
   ->{0,2,3}->{0,3}->{0}.                            (24.4)
```

When player `0` is fixed present, the three induced Quit advantages at a
product root `(p_1,p_2,p_3)` are exactly

```text
Delta_1=1-2*p_3,
Delta_2=2*p_1-1,
Delta_3=2*p_2-1.                                    (24.5)
```

Consequently the induced binary game has the unique Nash equilibrium

```text
p_1=p_2=p_3=1/2.                                    (24.6)
```

In fact every punishment value is zero.  Every payoff to a player absent from
the terminal coalition is nonnegative, so Never guarantees zero.  The
following sure opponent coalitions make both Continue and the best Quit
endpoint at most zero:

```text
player 0: {1,3},      player 1: {3},
player 2: {0},        player 3: {0,1}.               (24.6a)
```

For example player `0` gets Continue payoff `r_{1,3}(0)=0` and Quit payoff
`r_{0,1,3}(0)=-10`.  Hence `chi_i=0` for every `i`.  At (24.6), player `0`'s
prescribed payoff while fixed present is

```text
V_0=-13/8,
```

whereas the singleton-base leave expression is

```text
L_0=1/8.
```

Thus the unique induced Nash point has exact base-leave gap

```text
L_0-V_0=7/4.                                         (24.7)
```

Despite (24.3)--(24.7), the full terminal membership orientation has no pure
sink and no directed four-cycle.  Number coalitions by their bit masks from
`0` to `15`.  One outgoing coordinate at each vertex is

```text
0:0, 1:1, 2:0, 3:2, 4:0, 5:1, 6:0, 7:3,
8:0, 9:3, 10:1, 11:0, 12:0, 13:2, 14:2, 15:0.       (24.8)
```

For a square on coordinates `i<j` with fixed background `A`, write its sign
word as

```text
(epsilon_i(A), epsilon_j(A+i), epsilon_i(A+j), epsilon_j(A)),
```

where `+` means absent-to-present.  In the increasing two-bit order for the
background, the 24 square words are

```text
01: ++++, ++++, +---, +--+
02: +-++, +++-, +-+-, -+--
03: +-++, +--+, ++++, ++-+
12: +-++, +++-, --+-, -+--
13: ++-+, +---, ++++, ++-+
23: ++-+, -+--, -+-+, +++-.                         (24.9)
```

A directed square would have word `++--` or `--++`; neither occurs.

Proof.  The packet and crossed calculations are direct from (24.1).  For
(24.5), each player's Quit advantage depends on only the displayed predecessor
rate.  If `p_1<1/2`, best responses force successively `p_2=0`, `p_3=0`, and
`p_1=1`, a contradiction; the case `p_1>1/2` is symmetric, and
`p_1=1/2` forces `p_2=p_3=1/2`.  This proves (24.6).  Uniform averaging of
player `0`'s eight present-face payoffs

```text
1,2,1,1,1,-10,1,-10
```

gives `-13/8`; after leaving, only the nonempty cell `{1}` pays one, giving
`1/8`.  Equations (24.8)--(24.9) are the exhaustive 16-vertex and 24-square
checks.

This is not a counterexample to uniform equilibrium and does not supply a
terminal exploitability witness.  It is an exact local-interface regression:
crossed packet data, the full-gap preemption signs at `g=1`, exact zero
punishment values, a persistent strict cycle, and the full A.2 induced-Nash
gap do not force a pure terminal compiler or a strict matching-pennies square.
Any theorem closing repeated stable-pair exchange must use still more of the
packet/principal structure or a longer-cycle all-behavior compiler, not just
the orientation of cube edges and the punishment scalars.

### Proposition 24.2 (the size-two principal screen is also saturated)

For the table (24.1), the normalized singleton matrix, in player order
`0,1,2,3`, is

```text
M = [ 0  0 -1 -1
      0  0 -1 -1
     -1  1  0 -1
      1 -1 -1  0 ].                                  (24.10)
```

Each of the three size-two principals allowed by the checked crossed-packet
screen is exactly

```text
M[{0,2}]=M[{1,3}]=M[{2,3}]=[0 -1; -1 0].            (24.11)
```

All three are nonprojective.  Indeed the matrix in (24.11) has no homogeneous
simplex solution: any nonzero nonnegative weight makes the other coordinate
of the residual strictly negative.  It is not standard `Q`, because each row
has no positive entry, contradicting the checked necessary row-positivity
condition.  The exact convention split
`isProjectiveQMatrix_iff_standard_or_homogeneous` therefore excludes
projective `Q`.

Thus even the existence of an allowed two-player nonprojective principal does
not remove the regression.  The three safe pairs `{0,1},{0,3},{1,2}` remain
projective exactly as required by
`nonprojectivePrincipal_ne_safePairs_of_support_eq_pair`; (24.11) realizes
all complementary allowed pairs instead.  This says nothing about a theorem
which forces a particular size-three or size-four principal together with
additional decoder data.

### Proposition 24.3 (consumer audit: this regression is homogeneous-solved)

The preceding table is **not** a witness in the live LCP hard class.  Its
packet mass

```text
w=(1/2,1/2,0,0)
```

satisfies

```text
M*w=0.                                                (24.12)
```

Both positive-weight owners are punishment-normal because
`chi_0=chi_1=0<1`.  Hence the checked theorem

```text
exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal
```

in
`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`
accepts (24.1) directly and produces a uniform-equilibrium payoff.  The
orientation regression cannot therefore be used as a counterexample to the
maintained semantic dispatch.

For completeness, the larger principal audit is:

```text
projective by the same homogeneous support: {0,1,2}, {0,1,3}, {0,1,2,3};
nonprojective:                           {0,2,3}, {1,2,3}. (24.13)
```

For each nonprojective triple, the row belonging to `0` or `1` has only the
two entries `-1` off the diagonal, forcing those two weights to zero in any
nonnegative homogeneous residual; a remaining row then forces the last
weight to zero.  The same row has no positive entry, so standard `Q` is also
impossible.  Thus the full matrix fails projective `Q-bar`, but this does not
put the game in `ResidualHardClass`: its normal core is the full matrix and
already has the homogeneous solution (24.12), violating the hard class's
`no_homogeneous` field.

The instant-punishment singleton branch is not what solves the table.  Every
singleton has a strict outsider join, as witnessed by the outgoing labels in
(24.8), so no supported singleton passes the no-join test.  The correct
consumer is precisely the nonvertex homogeneous producer.

Accordingly Propositions 24.1--24.2 are a sharp falsifier only for an
**orientation-only stable-pair argument**.  They prove that adding more local
square completions cannot be the missing theorem.  They do not show that the
checked packet/principal consumers are exhausted.

## 25. A genuine residual-hard crossed-packet boundary

The homogeneous failure of Proposition 24 can be repaired without losing the
crossed packet.  The resulting table does **not** satisfy the terminal
exploitability witness and is not a counterexample.  Its purpose is sharper:
it shows that the crossed packet, the full residual-hard LCP data, exact
punishment floors, absence of pure terminal sinks, and failure of the
full-support stationary compiler are mutually compatible.  Moreover its only
two strict four-cycles both land in the explicit blocker-continuation failure
arm of (10.9).

Declarations inspected for this boundary test are:

```text
IsStandardQMatrix, HasHomogeneousSimplexSolution,
IsProjectiveQBarMatrix
  (Quitting/Classification/LCP/MatrixClasses.lean),
ResidualHardClass
  (Quitting/Classification/LCP/Gate.lean),
pairedSingletonMatrix_not_projectiveQBar
  (Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean),
QuittingNormalizedSingletonSourcePacket
  (Quitting/Classification/ThreePlayer/AnalyticPacket.lean),
QuittingInstantPunishmentεEquilibriumExistence
  (Quitting/Classification/ExistenceBranches.lean).
```

All claims in this section are ordinary mathematics, not new Lean
declarations.

### Proposition 25.1 (an exact residual-hard crossed matrix)

Let

```text
M = [ 0  3 -1  3
      2  0  1 -3
     -2  2  0 -1
      3 -2  1  0 ].                                  (25.1)
```

Then all four coordinates belong to the recursive normal core, `M` has no
homogeneous simplex-LCP solution, `M` is standard `Q`, and `M` is not
projective `Q-bar`.

Proof.  The negative witnesses in rows `0,1,2,3` are respectively columns
`2,3,0,1`; hence every coordinate survives every normal layer.

Every principal determinant of size at least two is nonzero.  In lexicographic
subset order they are

```text
01:-6, 02:-2, 03:-9, 12:-2, 13:-6, 23:1,
012:-10, 013:-39, 023:-3, 123:-4, 0123:-23.          (25.2)
```

Thus a homogeneous complementary solution cannot have support of size at
least two.  A singleton support is also impossible: columns `0,1,2,3` have
negative entries in rows `2,3,0,1`, respectively.  This proves the
nonhomogeneous assertion.

For the standard-`Q` assertion use the complementarity map

```text
Phi(x)=x^+-M x^-.
```

The preceding nonhomogeneous result implies `Phi^{-1}(0)={0}`.  Positive
homogeneity and compactness of the unit sphere therefore make `Phi` proper.
At the rational regular value

```text
q*=(1,1,2,1),
```

exact support enumeration leaves precisely three preimages:

```text
negative support       w on that support       outside residual
empty                  empty                   (1,1,2,1)
{0,2}                  (1,1)                   (4,5) on {1,3}
{1,3}                  (1/2,1/3)               (7/2,8/3) on {0,2}. (25.3)
```

For reproducibility, the remaining nonsingleton support solutions are

```text
01=(-1/2,-1/3),       12=(-1,-1),
012=(1/5,-4/5,-7/5), 03=(-1/3,-1/3),
013=(-7/13,-4/13,-1/39),
23=(-1,2) with a negative outside residual,
023=(8/3,-9,-10/3),  123=(-3/2,-4,-1),
0123=(10/23,-22/23,-97/23,-18/23).                  (25.4)
```

Singleton supports are inconsistent because `q*_i>0`.  The derivative
determinants at the three feasible preimages are `1,-2,-6`, so the total
degree is `1-1-1=-1`.  Properness and homotopy invariance give nonzero degree
at every right-hand side.  Hence every standard LCP has a solution and `M`
is standard `Q`.

Finally the principal pair `{0,2}` is

```text
[0 -1; -2 0].                                        (25.5)
```

For projective right-hand side `(-1,-1)`, if the cemetery weight is `c` and
the two singleton weights are `x,z`, residual nonnegativity gives
`-c-z>=0` and `-c-2x>=0`.  Nonnegativity forces `c=x=z=0`, contradicting
their total mass one.  Thus this principal is nonprojective and the full
matrix is not projective `Q-bar`.  Together with the full normal core, (25.1)
therefore realizes the exact matrix fields of `ResidualHardClass`.  QED.

### Proposition 25.2 (literal reward table, packet, and floors)

Define a rational four-player reward table as follows.  Its complete list of
nonempty-coalition payoff vectors is

```text
0:(1,3,-1,4)       1:(4,1,3,-1)       01:(1,1,20,2)
2:(0,2,1,2)        02:(1,4,1,5)       12:(10,1,1,0)
012:(1,5,1,3)      3:(4,-2,0,1)       03:(1,0,-2,1)
13:(7,1,2,1)       013:(1,1,0,1)      23:(3,-1,1,1)
023:(1,1,1,1)      123:(6,-2,5,1)     0123:(1,1,1,1). (25.6)
```

Here, for example, `01` denotes coalition `{0,1}`.  Its normalized singleton
matrix is exactly (25.1), since every own singleton payoff is one.

Put packet mass `1/2` on each of owners `0,1`, zero on `2,3`, and take target

```text
v=(1,1,1,1).
```

The singleton mixture is

```text
(r_0+r_1)/2=(5/2,2,1,3/2)>=v.                       (25.7)
```

The positive owners are pinned because `v_0=r_0(0)=1` and
`v_1=r_1(1)=1`; every solo payoff is also one.  The crossed outsiders are
literal:

```text
r_0(2)=-1 < 1 < 3=r_1(2),
r_1(3)=-1 < 1 < 4=r_0(3).                           (25.8)
```

The punishment floors are at most one.  Against player `i`, let respectively
opponents `2,3,0,1` Quit surely.  If `i` Continues its payoff is
`0,-2,-1,-1`; if it Quits too its payoff is one.  Since the opponent stops
at the first row, this controls every behavioral deviation of `i`, and gives
`chi_i<=1=v_i`.  For `i=0,2`, every coalition containing `i` pays that player
at least one, so immediate Quit also gives `chi_0=chi_2=1`.

Thus (25.7)--(25.8), including the unrestricted punishment bound, define an
exact `QuittingNormalizedSingletonSourcePacket` with support `{0,1}` inside
the residual-hard matrix chamber of Proposition 25.1.  QED.

### Proposition 25.3 (no pure sink, and the two four-cycle residuals)

Every pure terminal coalition, including `Never`, has a unilateral toggle of
gain at least one.  One complete choice is

```text
Never->0,  0->02,  1->13,  2->02,  3->13,
01->1,     02->012, 03->3, 12->2, 13->123, 23->2,
012->12,   013->13, 023->23, 123->23, 0123->123.     (25.9)
```

Direct subtraction in (25.6) gives gains, in the same order,

```text
1,2,2,1,3,3,1,3,1,3,1,9,6,2,1,5.
```

For the cycle assertion, the complete positive-toggle adjacency list is

```text
Never:{0,1,2,3};  0:{02}; 1:{13}; 2:{02}; 3:{13,23};
01:{0,1}; 02:{012}; 03:{3,013,023,0};
12:{2,1,123}; 13:{123}; 23:{2};
012:{12,01}; 013:{13,0123,01};
023:{23,02}; 123:{23}; 0123:{123,012}.              (25.9a)
```

Here the entries are target coalitions, not toggling-player labels.  Direct
enumeration of four-step returns in (25.9a) leaves exactly two simple
four-cycles:

```text
C_0: 0 -> 02 -> 012 -> 01 -> 0,
C_2: 2 -> 02 -> 012 -> 12 -> 2.                    (25.10)
```

Both fall in the explicit blocker-continuation failure arm of (10.9), rather
than into the sure-blocker compiler.

For `C_0`, the persistent blocker is `0` and the active players are `1,2`.
Their unique induced matching-pennies root has

```text
p_1=2/21,       p_2=2/3.                            (25.11)
```

The blocker receives `V_0=1` if it Quits.  If it Continues, the four
opponent outcomes `empty,{1},{2},{1,2}` have probabilities

```text
19/63, 2/63, 38/63, 4/63
```

and payoffs `chi_0=1,4,0,10`.  Its continuation value is therefore

```text
(19+8+40)/63=67/63=1+4/63>V_0.                      (25.12)
```

For `C_2`, the blocker is `2`, the active players are `0,1`, and the unique
induced root is

```text
p_0=1/2,        p_1=1/10.                           (25.13)
```

Again `V_2=1`.  The probabilities of
`empty,{0},{1},{0,1}` are `9/20,9/20,1/20,1/20`, and the corresponding
continuation payoffs are `chi_2=1,-1,3,20`.  Thus

```text
(9-9+3+20)/20=23/20=1+3/20>V_2.                    (25.14)
```

Equations (25.12) and (25.14) are exact instances of the second disjunct in
(10.9).  They also show why checking only pure terminal sinks would miss the
semantic residual.  QED.

### Proposition 25.4 (the full-support stationary polynomial has no root)

The table also lies in the exact empty-base residual (15.3) when all four
players are declared active.  For the baseline rule

```text
r_S(i)=1                         if i in S,
r_S(i)=1+sum_(j in S) M_ij       if i notin S,       (25.15)
```

one has `H_i(p)=-(Mp)_i`.  The exceptions in (25.6) affect only their named
player's polynomial.  In particular

```text
H_0=p_2-3p_1-3p_3-7p_1p_2(1-p_3),
H_3=-3p_0+2p_1-p_2.                                 (25.16)
```

If all rates are strictly between zero and one and `H_3=0`, then

```text
p_2=2p_1-3p_0<2p_1.
```

Substitution into the first line of (25.16) gives

```text
H_0 < -p_1-3p_3 <0.
```

Hence `H_0=H_3=0` is already impossible, independently of the other two
equations.  No full-support interior stationary compiler exists.  QED.

### Proposition 25.5 (a different support is accepted exactly)

The preceding obstruction is genuinely full-support only.  In fact the same
table has an exact stationary compiler on active set `{1,2,3}`, with player
`0` passive.

Put

```text
p_0=0,       p_1=x,       p_2=2x,       p_3=z.
```

Direct expansion of (12.2) gives

```text
H_1=3z-2x-6xz^2-12x^2z+12x^2z^2,
H_2=z-2x+4xz^2+4x^2z-4x^2z^2,
H_3=0,                                               (25.17)
```

and

```text
H_1-3H_2
 =2x[2-9z^2-12xz(1-z)].                             (25.18)
```

For `7/20<=z<=3/8`, define

```text
x(z)=(2-9z^2)/(12z(1-z)).                            (25.19)
```

This is continuous and satisfies `0<x(z)<1/2`, so all three declared active
rates lie in `(0,1)`.  Multiplying `H_2(x(z),z)` by the positive square of the
denominator in (25.19) gives

```text
P(z)=-32z+32z^2+312z^3-456z^4+36z^5+108z^6.         (25.20)
```

Exact endpoint arithmetic yields

```text
P(7/20)=-5731817/16000000<0,
P(3/8)=32955/65536>0.                                (25.21)
```

The intermediate value theorem therefore gives a `z_*` in that interval
with `P(z_*)=0`.  Taking `x_*=x(z_*)`, equations (25.17)--(25.20) give

```text
H_1=H_2=H_3=0.
```

For the passive player,

```text
H_0=-3z_*-x_*-14x_*^2(1-z_*)<0.                     (25.22)
```

Thus the passive no-join inequality holds strictly.  Proposition 12.1 applies
with `F={1,2,3}` and `O={0}`.  The three positive active rates give every
player the required opponent contraction, so this is an exact terminal Nash
profile against unrestricted behavioral deviations and supplies a uniform-
equilibrium payoff.  QED.

### Exact scope of the boundary

Propositions 25.1--25.4 do **not** supply a terminal exploitability witness.
Proposition 25.5 positively exhibits the missing different-support stationary
equilibrium.  In particular, `ResidualHardClass` is algebraic data, not
counterexamplehood, and failure of the cycle-face/full-support stationary
tests is not a strategy-class completeness statement.

What the table proves is the following exact negative screen.  None of these
additional inputs alone eliminates the final cycle chamber:

```text
crossed support-two packet;
all-player punishment normality;
standard-Q/no-homogeneous/full-non-Q-bar matrix data;
absence of pure terminal sinks;
absence of a full-support stationary root;
the complete four-cycle compiler test.
```

The missing input must use the maintained terminal exploitability witness or
more detailed punishment-strategy semantics, rather than only its scalar
floor values and the principal singleton matrix.  It must also rule out the
kind of transverse active-support change constructed in Proposition 25.5.

## 26. Exact quantifier elimination of the large-persistent-base gap

The maintained checked semantic dispatch has one large-base residual:
`|B|>=2` and the literal leave/join excess `G` is uniformly positive on the
induced Nash set.  In four players this apparently compact residual is only a
two-by-two calculation.

Indeed, the strict-toggle face has at least two free labels, while `B` and the
free face `F` are disjoint.  Hence

```text
|B|=|F|=2,              O=empty.                    (26.1)
```

Write `B={a,b}` and `F={x,y}`.  Encode Continue by `0` and Quit by `1`, and
put

```text
C_ij = B union ({x} if i=1) union ({y} if j=1),
X_ij = r_(C_ij)(x),       Y_ij = r_(C_ij)(y),

alpha_j = X_1j-X_0j,      beta_i = Y_i1-Y_i0.        (26.2)
```

For `c in B`, define the exact leave gain at that cell by

```text
ell_c^ij = r_(C_ij\{c})(c)-r_(C_ij)(c).             (26.3)
```

The coalition in the first term is nonempty because the other base member
remains.

### Proposition 26.1 (finite large-base alternative)

Assume that for some `gamma>0`, every Nash equilibrium of the induced binary
game on `{x,y}` has large-base excess at least `gamma`.  Then exactly one of
the following two finite outputs is available.

1. **Internally stable pure vertex with a paid base leave.**  There are
   `i,j in {0,1}` and `c in B` such that

   ```text
   (-1)^(1-i) alpha_j >= 0,
   (-1)^(1-j) beta_i  >= 0,
   ell_c^ij >= gamma.                               (26.4)
   ```

   Here the first two inequalities mean precisely that `(i,j)` is a pure
   Nash cell.  The last inequality is a strict selected toggle
   `C_ij -> C_ij\{c}` whose source is already stable under both free-label
   toggles.

2. **Strict matching-pennies cell with a division-free paid leave.**  There
   is no pure Nash cell, the four differences obey one of the two strict sign
   patterns

   ```text
   alpha_0>0>alpha_1,   beta_1>0>beta_0,            (26.5+)
   alpha_1>0>alpha_0,   beta_0>0>beta_1,            (26.5-)
   ```

   and for some `c in B`,

   ```text
   N_c >= gamma D > 0,                              (26.6)

   D   =(alpha_0-alpha_1)(beta_1-beta_0),
   N_c =(-beta_1 alpha_1) ell_c^00
        +( beta_0 alpha_1) ell_c^10
        +( beta_1 alpha_0) ell_c^01
        +(-beta_0 alpha_0) ell_c^11.
   ```

   In either sign pattern `D>0`.  Thus (26.6) is a division-free polynomial
   inequality in the pair, triple, and grand-coalition rewards.

#### Proof

If the induced game has a pure Nash cell `(i,j)`, evaluate the supplied
large-base gap at its pure product distribution.  There are no outside
players and the two free components of `G` are zero by definition.  Hence
some `c in B` satisfies `ell_c^ij>=gamma`, proving the first output.

Suppose there is no pure Nash cell.  None of `alpha_0,alpha_1,beta_0,beta_1`
can vanish.  For example, if `alpha_0=0`, then `beta_0<=0` makes `(0,0)` a
pure Nash cell.  Otherwise `beta_0>0`; if `alpha_1<=0`, `(0,1)` is pure Nash,
while if `alpha_1>0`, either `beta_1<=0` makes `(1,0)` pure Nash or
`beta_1>=0` makes `(1,1)` pure Nash.  The other three zero cases are the same
argument after exchanging rows, columns, or players.  If `alpha_0` and
`alpha_1` had the same sign, `x` would have one strict best action against
both columns; a pure best response of `y` to that row would again give a pure
Nash cell.  Thus the `alpha` signs are opposite.  Following strict best
responses around the four cells forces the corresponding opposite `beta`
signs, giving exactly (26.5+) or (26.5-).

No equilibrium can then have a pure coordinate: the other player's pure best
response would create a pure Nash cell (and indifference is excluded).  The
unique equilibrium is therefore fully mixed.  If

```text
s=Pr(x Quits),       t=Pr(y Quits),
```

the two indifference equations give, in both orientations,

```text
s=-beta_0/(beta_1-beta_0),
t= alpha_0/(alpha_0-alpha_1).                       (26.7)
```

All four product weights are strictly positive.  With the common positive
denominator `D`, they are respectively

```text
w_00=(-beta_1 alpha_1)/D,
w_10=( beta_0 alpha_1)/D,
w_01=( beta_1 alpha_0)/D,
w_11=(-beta_0 alpha_0)/D.                           (26.8)
```

Consequently the expected leave gain of base member `c` is exactly `N_c/D`.
Applying the assumed gap at this unique mixed Nash equilibrium gives a base
member with `N_c/D>=gamma`, which is (26.6).  QED.

### Scope and interface

Proposition 26.1 is an exact finite elimination of the quantifier over the
large-base induced Nash set; it is not another generic cycle recollection.
The pure branch records an internally stable coalition with one quantitatively
paid base-leave toggle.  The mixed branch is precisely the two-blocker
matching-pennies face of Proposition 10.2, but now its failed leave check is
the explicit polynomial numerator (26.6), with no selected rates or division
left in the output.

Neither branch is itself an all-behavior compiler: the paid base leave is the
reason the sure-base root fails.  Nor does the result address the singleton-
base or empty-base semantic gaps.  Its value is that the large-base arm of
the authoritative semantic residual has only eight pure certificates and two
strict matching-pennies sign chambers (each with one of two paid base labels),
all stated directly in finite reward-table data.

### Proposition 26.2 (delete the paid base member: exact singleton-base handoff)

The mixed branch has a nontrivial checked compiler subchamber.  Retain the
notation above and choose `c in B` satisfying (26.6); write `B={c,d}`.  For
the base-deleted square define

```text
D_ij={d} union ({x} if i=1) union ({y} if j=1),

bar_alpha_j = r_(D_1j)(x)-r_(D_0j)(x),
bar_beta_i  = r_(D_i1)(y)-r_(D_i0)(y),              (26.9)

R_x=-alpha_1 bar_alpha_0+alpha_0 bar_alpha_1,
R_y= beta_1 bar_beta_0-beta_0 bar_beta_1.            (26.10)
```

Use the positive weight numerators from (26.8), so that

```text
W_00=-beta_1 alpha_1,   W_10= beta_0 alpha_1,
W_01= beta_1 alpha_0,   W_11=-beta_0 alpha_0,
sum W_ij=D.                                             (26.11)
```

Finally define the punishment-priced blocker numerator

```text
K_d = W_00 chi_d+W_10 r_x(d)+W_01 r_y(d)+W_11 r_{x,y}(d)
      -sum_(i,j) W_ij r_(D_ij)(d).                    (26.12)
```

If

```text
R_x=0,             R_y=0,             K_d<=0,         (26.13)
```

then the root at which `d` Quits surely, `x,y` use the same interior rates
`s,t` from (26.7), and `c` Continues is accepted by the checked singleton-base
all-behavior compiler.  Consequently, under a terminal exploitability
witness, every mixed large-base residual satisfies the exact smaller
disjunction

```text
R_x != 0       or       R_y != 0       or       K_d>0. (26.14)
```

#### Proof

The first equality in (26.13), divided by the nonzero
`alpha_0-alpha_1`, is exactly

```text
(1-t)bar_alpha_0+t bar_alpha_1=0.
```

The second equality, divided by `beta_1-beta_0`, is exactly the analogous
indifference equation for `y`.  Since `s,t` are strictly interior, these two
equalities say that their product mixture is an exact Nash equilibrium of
the induced binary game with persistent base `{d}`.

Player `c` is now the sole outsider.  Its Continue payoff at the displayed
root is

```text
V_c^-=(1/D) sum_(i,j) W_ij r_(D_ij)(c),
```

whereas joining at date zero gives

```text
V_c^+=(1/D) sum_(i,j) W_ij r_(C_ij)(c).
```

By (26.3), (26.6), and (26.8),

```text
V_c^- - V_c^+ = N_c/D >= gamma.                    (26.15)
```

Thus the outsider no-join inequality holds with a strict quantitative
margin; deleting the paid base member has turned its failed leave check into
the correct spectator check.

It remains only to control the sure owner `d`.  If `d` Continues, the three
nonempty `x,y` action sets absorb at `{x}`, `{y}`, or `{x,y}`.  The joint-
Continue cell reaches an accuracy-dependent punishment tail priced at
`chi_d`.  Therefore `K_d/D` is exactly
`quittingSingletonBaseOwnerFloorExcess` at this root.  The last inequality in
(26.13) is precisely the owner-floor balance.  The exact induced Nash
equalities, the outsider check (26.15), and this floor check instantiate
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`; its
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` consumer covers
all behavioral deviations.  A terminal witness excludes that conclusion,
so (26.14) follows.  QED.

This adapter is genuinely source-specific.  It does not assert that deleting
`c` preserves the free-player game: the two explicit reprojection residuals
`R_x,R_y` measure exactly that failure.  When it does preserve the one mixed
root, the already paid leave automatically supplies the missing outsider
inequality, leaving only the named punishment premium `K_d`.

## 27. Pure paid-leave cells have the same exact singleton-base handoff

Take the pure output `(i,j,c)` of Proposition 26.1, write `B={c,d}`, and let

```text
R_ij=({x} if i=1) union ({y} if j=1),
C_ij={c,d} union R_ij,
D_ij={d} union R_ij.                                (27.1)
```

Define the base-deleted pure endpoint differences

```text
bar_alpha_j=r_(D_1j)(x)-r_(D_0j)(x),
bar_beta_i =r_(D_i1)(y)-r_(D_i0)(y),                (27.2)
```

using the same notation `D_kl={d} union ({x} if k=1) union
({y} if l=1)`.  Say that the retained actions are stable after deletion when

```text
i=0 -> bar_alpha_j<=0,       i=1 -> bar_alpha_j>=0,
j=0 -> bar_beta_i <=0,       j=1 -> bar_beta_i >=0. (27.3)
```

Finally put

```text
K_d^ij =
  if R_ij=empty then chi_d-r_{d}(d)
  else r_(R_ij)(d)-r_(D_ij)(d).                    (27.4)
```

### Proposition 27.1 (pure-cell deletion compiler)

If the two retained-action signs (27.3) hold and `K_d^ij<=0`, then the root
at which `d` Quits surely, `x,y` play the pure actions `(i,j)`, and `c`
Continues is accepted by the checked singleton-base all-behavior compiler.
Consequently, under a terminal exploitability witness, every pure output of
Proposition 26.1 belongs to the strictly smaller finite residual

```text
(i=0 and bar_alpha_j>0) or (i=1 and bar_alpha_j<0)
or
(j=0 and bar_beta_i>0) or (j=1 and bar_beta_i<0)
or
K_d^ij>0.                                           (27.5)
```

#### Proof

Conditions (27.3) say exactly that the pure point `(i,j)` is an induced Nash
equilibrium of the free binary game with persistent base `{d}`.  Player `c`
is its sole outsider.  Its Continue payoff is `r_(D_ij)(c)`, while joining
gives `r_(C_ij)(c)`.  The paid leave from Proposition 26.1 therefore gives

```text
r_(D_ij)(c)-r_(C_ij)(c)=ell_c^ij>=gamma>0.          (27.6)
```

Thus the outsider no-join field holds strictly.

If `R_ij` is nonempty, at least one retained free player Quits surely.  When
`d` Continues the date-zero coalition is exactly `R_ij`, so its owner-floor
Continue-minus-Quit excess is

```text
r_(R_ij)(d)-r_(D_ij)(d).
```

If `R_ij` is empty, everyone else Continues and the owner continuation is
priced at the exact punishment value `chi_d`; the excess is
`chi_d-r_d(d)`.  Hence (27.4) is exactly
`quittingSingletonBaseOwnerFloorExcess` at the displayed root.

The induced Nash signs, (27.6), and `K_d^ij<=0` instantiate
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  Its checked
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` consumer covers
unrestricted behavioral deviations, using accuracy-dependent punishment
only in the `R_ij=empty` cell.  A terminal witness excludes this output, and
the literal negation of the two weak signs and the floor inequality is
(27.5).  QED.

### Proposition 27.2 (a nonempty owner premium descends to a sure-exit test)

Continue with a pure paid cell and suppose `R_ij` is nonempty and
`K_d^ij>0`.  Extend the reward notation to the empty set by

```text
hat_r_empty=0,       hat_r_S=r_S for S nonempty.
```

If

```text
hat_r_(R_ij\{z})(z) <= r_(R_ij)(z)       for every z in R_ij,
r_(R_ij union {z})(z) <= r_(R_ij)(z)     for every z in F\R_ij,
r_(R_ij union {c})(c) <= r_(R_ij)(c),                (27.7)
```

then `R_ij` is an exact sure-exit set and `r_(R_ij)` is a uniform-equilibrium
payoff.  Therefore, under a terminal exploitability witness, the nonempty
premium chamber has the finite residual

```text
some z in R_ij has hat_r_(R_ij\{z})(z)>r_(R_ij)(z),
or some z in F\R_ij has r_(R_ij union {z})(z)>r_(R_ij)(z),
or r_(R_ij union {c})(c)>r_(R_ij)(c).               (27.8)
```

#### Proof

Since `R_ij` is nonempty, (27.4) and the strict premium give

```text
r_(R_ij)(d)>r_({d} union R_ij)(d).                  (27.9)
```

Thus after deleting `d`, that former owner leave becomes `d`'s strict
outsider no-join inequality at the pure exit set `R_ij`.  The first line of
(27.7) is exactly the no-leave test for every member of the exit set, including
the singleton case through `hat_r_empty=0`.  The second line controls every
other free label, the third controls `c`, and (27.9) controls the only
remaining player `d`.  Hence all four membership-toggle inequalities in
`IsQuittingSureExitSet reward R_ij` hold.  The checked theorem
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` supplies the
all-behavior uniform payoff.  A terminal witness excludes it, and negating
the finite conjunction gives (27.8).  QED.

### Combined large-base status

Propositions 26.2 and 27.1 now consume one exact subchamber in **both** outputs
of the large-base quantifier elimination.  After deleting the paid base
member, its old leave is never a new obstacle: it becomes the needed strict
outsider inequality.  The only remaining data are

```text
pure:  two retained-action sign failures or one punishment premium;
mixed: two retained-indifference seams or one punishment premium.
```

Proposition 27.2 further consumes every nonempty pure premium cell that passes
the exact sure-exit membership tests, leaving only the three explicit toggle
failures (27.8).  The all-Continue pure cell `R_ij=empty` is deliberately
separate: there `K_d^ij>0` compares the owner's solo payoff with `chi_d` and
does not create a nonempty exit set.

These are smaller polynomial/punishment chambers attached to the actual paid
label; no cycle geometry or stationary-support completeness is being assumed.

## 28. Next question

### Proposition 28.1 (a retained-sign failure has one exact binary repair)

Take a pure paid cell `(i,j,c)` from Proposition 26.1, write `B={c,d}`, and
suppose one retained-action sign in (27.3) fails.  After exchanging `x,y` if
needed, suppose it is the `x` sign.  Keep `y` at its old action `j`.  Encode
the old `x` action `i` by `e=0` and the opposite action `1-i` by `e=1`; encode
absence/presence of `c` by `h=0,1`.  Let

```text
S_he={d}
     union ({c} if h=1)
     union ({x} if (i xor e)=1)
     union ({y} if j=1),                             (28.1)

J_e=r_(S_1e)(c)-r_(S_0e)(c),
E_h=r_(S_h1)(x)-r_(S_h0)(x).                         (28.2)
```

Here `xor` is binary addition modulo two.  The old paid leave, the failed
base-deleted sign, and the old retained-action stability say exactly

```text
J_0<=-gamma<0,             E_0>0,             E_1<=0. (28.3)
```

The induced binary game of `{c,x}` against the fixed background `{d}` and
the fixed `y` action has the following exhaustive, relabeling-invariant Nash
selection.

```text
J_1<=0:                 choose the pure cell (h,e)=(0,1);
J_1>0 and E_1=0:        choose the pure cell (h,e)=(1,1);
J_1>0 and E_1<0:        choose the unique interior mixed cell.       (28.4)
```

In the mixed case put

```text
H=(E_0-E_1)(J_1-J_0)>0,

W_00=(-E_1)J_1,       W_10=E_0 J_1,
W_01=E_1 J_0,         W_11=-E_0 J_0.                (28.5)
```

Then every `W_he` is positive, their sum is `H`, and `W_he/H` are the four
product weights.  In either pure case instead put `H=1` and put unit weight
on the selected cell in (28.4), with all other `W_he=0`.

For the remaining free label `y`, define its endpoint difference at each
`c,x` cell by

```text
Delta_y^he = r_(O_he union {y})(y)-r_(O_he)(y),
O_he=S_he\{y}.                                       (28.6)
```

The set `O_he` is nonempty because it contains `d`.  Define the owner-floor
cell excess using

```text
T_he=S_he\{d},
p_d(T)=chi_d if T=empty, and p_d(T)=r_T(d) otherwise,
k_d^he=p_d(T_he)-r_(T_he union {d})(d),              (28.7)

N_y=sum_(h,e) W_he Delta_y^he,
K_d=sum_(h,e) W_he k_d^he.                           (28.8)
```

If

```text
j=0 -> N_y<=0,             j=1 -> N_y>=0,
K_d<=0,                                                     (28.9)
```

then the root at which `d` Quits surely, `{c,x}` use the Nash selection
(28.4), and `y` uses its pure action `j` is accepted by the checked
singleton-base all-behavior compiler.  Consequently, under a terminal
exploitability witness, every pure base-deletion sign failure belongs to one
of the three explicit face types in (28.4) and, for its selected weights,
to the exact smaller residual

```text
(j=0 and N_y>0) or (j=1 and N_y<0) or K_d>0.          (28.10)
```

#### Proof

At `e=0`, the old paid leave is precisely `-J_0>=gamma`.  At `h=0`, failure
of the retained old action says that `x` strictly prefers the opposite
action, so `E_0>0`.  At `h=1`, the original pure induced-Nash sign says the
old action is weakly preferred, so `E_1<=0`.  This proves (28.3).

If `J_1<=0`, at `(h,e)=(0,1)` player `x` is strictly stable by `E_0>0` and
player `c` is weakly stable absent by `J_1<=0`.  If `J_1>0` and `E_1=0`, at
`(1,1)` player `c` is strictly stable present and player `x` is indifferent.
These are the first two Nash cells in (28.4).

In the remaining case the signs are

```text
J_0<0<J_1,                 E_1<0<E_0,
```

so the binary game is strict matching pennies and has no pure Nash cell.  Its
unique mixed equilibrium has

```text
Pr(c present)=E_0/(E_0-E_1),
Pr(e=1)=-J_0/(J_1-J_0).                              (28.11)
```

Multiplying the independent probabilities gives exactly (28.5); direct
addition gives `sum W_he=H`.  Thus in all three cases the selected weights
give an exact Nash profile for the `{c,x}` face.

The normalized expected endpoint difference of `y` is `N_y/H`.  The first
line of (28.9) says exactly that its fixed action `j` is also a best response.
There are no further free players or outsiders: the player set is
`{c,d,x,y}`, and `d` is the sure singleton-base owner.  If `d` deviates to
Continue, its payoff in cell `(h,e)` is `r_(T_he)(d)` when another player
Quits and is priced at `chi_d` when `T_he` is empty.  Hence its normalized
Continue-minus-Quit excess is exactly `K_d/H`, and the second line of (28.9)
is the owner-floor field.

The selected `{c,x}` Nash conditions, the `y` sign, and the owner-floor sign
therefore instantiate
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  The consumer
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` controls every
unrestricted behavioral deviation.  A terminal witness excludes this
output.  Since `H>0`, the literal negation of (28.9) is (28.10).  QED.

### Scope and next residual

Proposition 28.1 consumes the raw reprojection-sign disjunction in (27.5).
It does not freeze the old free actions after deletion: it re-equilibrates
exactly the paid former owner and the failed free label.  The first two arms
are weak-boundary pure cells and the third is one strict matching-pennies
cell with division-free positive weights.  The only remaining tests are the
other free label's single expected endpoint sign and the sure owner's exact
punishment-floor premium.  These are explicit pair/triple/grand-reward and
punishment-value inequalities, not another selected-toggle cycle.

The next question is whether a failed `N_y` sign can be promoted using the
still-paid edge `J_0<=-gamma`, or whether `K_d>0` descends to a sure-exit or
second singleton-base certificate.  The empty-cell premium and the mixed
residual (26.14) remain separate.

### Proposition 28.2 (a positive repaired owner premium has a pure sure-exit
descent)

Continue with any of the three Nash selections of Proposition 28.1.  Assume

```text
K_d=sum_(h,e) W_he k_d^he>0.                          (28.12)
```

Then there is a selected cell `(h,e)` with `W_he>0` such that

```text
H k_d^he >= K_d>0.                                   (28.13)
```

Put `T=T_he`.  Exactly one of the following finite outputs holds.

1. `T=empty`, and

   ```text
   chi_d-r_d(d)=k_d^he>=K_d/H>0.                     (28.14)
   ```

   This is the exact all-Continue owner-premium arm.
2. `T` is nonempty and is an exact sure-exit set.  Then `r_T` is accepted by
   `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` against
   unrestricted behavioral deviations.
3. `T` is nonempty, `d` has the strict outsider no-join margin

   ```text
   r_(T union {d})(d)+K_d/H <= r_T(d),               (28.15)
   ```

   and a different label supplies one of the literal failures

   ```text
   exists z in T,
     hat_r_(T\{z})(z)>r_T(z),
   or exists z notin T union {d},
     r_(T union {z})(z)>r_T(z).                      (28.16)
   ```

   Here `hat_r_empty=0` and `hat_r_A=r_A` for nonempty `A`.

Under a terminal exploitability witness item 2 is excluded, so every positive
owner-floor residual from Proposition 28.1 is reduced to the exact empty
premium (28.14) or the nonempty paid pure toggle residual (28.15)--(28.16).

#### Proof

The normalized weights `W_he/H` are nonnegative and sum to one in all three
selections.  Therefore some positive-weight cell has

```text
k_d^he >= sum_(a,b) (W_ab/H)k_d^ab=K_d/H,
```

which is (28.13).  If `T_he` is empty, the definition (28.7) gives (28.14).

Suppose `T` is nonempty.  Then (28.7) and (28.13) give

```text
r_T(d)-r_(T union {d})(d)=k_d^he>=K_d/H>0,
```

which is (28.15).  Thus after clearing `d`, player `d` satisfies the outsider
no-join inequality at `T` with a strict quantitative margin.

Test all remaining membership inequalities at `T`.  If every member `z in T`
weakly prefers its present membership, and every outsider `z notin T` weakly
prefers to remain out, these inequalities, including the already strict `d`
one, are exactly `IsQuittingSureExitSet reward T`.  The checked sure-exit
consumer gives item 2.  Otherwise `d` cannot be a failing outsider because of
(28.15), so negating the finite remaining conjunction gives exactly (28.16).
QED.

This proposition is an exact pure-cell extraction from the repaired mixed or
pure owner premium.  It does not claim that the selected cell was itself a
Nash cell of the repaired product law.  None is needed for the sure-exit test:
after clearing `d`, all four membership inequalities are tested literally at
the one nonempty coalition `T`.  The original paid edge
`J_0<=-gamma` remains part of the source data but is not used to manufacture
the distinct premium `K_d/H`.

### Proposition 28.3 (a wrong remaining-label numerator promotes to a pure
sure-exit test)

Continue with Proposition 28.1 and suppose the remaining-label sign fails.
Define its oriented gain numerator by

```text
G_y=N_y   if j=0,
G_y=-N_y  if j=1.                                    (28.17)
```

Thus `G_y>0`.  There is a selected cell `(h,e)` with `W_he>0` such that,
writing

```text
g_he= Delta_y^he   if j=0,
g_he=-Delta_y^he   if j=1,                           (28.18)
```

one has

```text
H g_he>=G_y>0.                                       (28.19)
```

Let `P` be the coalition after `y` takes its preferred action at that cell:

```text
P=O_he union {y}  if j=0,
P=O_he            if j=1.                            (28.20)
```

The set `P` is nonempty because it contains `d`.  Exactly one of the following
finite outputs holds.

1. `P` is an exact sure-exit set, and `r_P` is a uniform-equilibrium payoff
   against unrestricted behavioral deviations.
2. The preferred `y` action is stable at `P` with margin at least `G_y/H`,
   while a different label supplies a strict failure

   ```text
   exists z in P, z!=y,
     hat_r_(P\{z})(z)>r_P(z),
   or exists z notin P, z!=y,
     r_(P union {z})(z)>r_P(z).                      (28.21)
   ```

Under a terminal exploitability witness only item 2 remains.  Thus the wrong
`y` numerator in (28.10) is converted to a quantitatively anchored pure
coalition at which `y` cannot be the next destabilizer.

#### Proof

If `j=0`, the failure in (28.10) is `N_y>0`, and

```text
N_y/H=sum_(h,e)(W_he/H) Delta_y^he.
```

If `j=1`, it is `N_y<0`, and the same identity after negation uses
`-Delta_y^he`.  In either case averaging over the nonnegative weights gives a
positive-weight cell satisfying (28.19).

For `j=0`, the preferred coalition is `P=O_he union {y}` and

```text
r_P(y)-r_(P\{y})(y)=Delta_y^he=g_he>=G_y/H.
```

Thus `y`, now a member, strictly prefers not to leave.  For `j=1`, the
preferred coalition is `P=O_he` and

```text
r_P(y)-r_(P union {y})(y)=-Delta_y^he=g_he>=G_y/H.
```

Thus `y`, now an outsider, strictly prefers not to join.  In both cases its
membership inequality at `P` holds with the displayed margin.

Test all other membership inequalities at `P`.  If they all hold, together
with the strict `y` inequality they are exactly
`IsQuittingSureExitSet reward P`, and the checked sure-exit consumer gives
item 1.  Otherwise the failed inequality cannot belong to `y`, so the finite
negation is exactly (28.21).  Equivalently, in the join case this is the
checked promotion theorem
`isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin`; the direct argument
also covers the leave case.  QED.

This is not a generic toggle collector.  It extracts one literal cell from
the exact repaired product weights, retains the quantitative wrong-sign
margin `G_y/H`, and removes the responsible label from the next failure.
It does not assert that repeated promotions terminate or that the resulting
second toggle enters a chronology.

### Proposition 28.4 (the empty premium forces a nonempty owner join)

Assume the four-player terminal exploitability witness and the empty owner
premium left by Propositions 27.1 or 28.2:

```text
r_d(d)<chi_d.                                          (28.22)
```

Then

```text
r_d(d)<0,                    chi_d<=0,                 (28.23)
```

and there is a nonempty coalition `T` of the other three players such that

```text
d notin T,               r_T(d)<r_(T union {d})(d).   (28.24)
```

Moreover, putting `P=T union {d}`, exactly one of the following checked
outputs holds:

1. `P` is a sure-exit set and `r_P` is a uniform-equilibrium payoff against
   unrestricted behavioral deviations;
2. some old member `z in T` strictly prefers to leave `P`; or
3. some outsider `z notin P` strictly prefers to join `P`.

Under the terminal witness item 1 is excluded.  Thus the abstract empty
punishment premium is replaced by a finite nonempty-coalition strict join by
`d`, followed by a strict toggle whose responsible label is not `d`.

#### Proof

Apply `quittingPunishmentValue_le_pureRowCap` to the empty pure row.  It gives

```text
chi_d<=max(r_d(d),0).                                  (28.25)
```

If `0<=r_d(d)`, then the right side is `r_d(d)`, contradicting (28.22).
Hence `r_d(d)<0`; substituting this back into (28.25) gives `chi_d<=0`.
This proves (28.23).

Now invoke
`QuittingTerminalExploitabilityWitness.exists_strict_owner_toggle_of_card_eq_four`
with owner `d`, (28.22), and `chi_d<=0`.  Its conclusion is exactly a
nonempty `T` satisfying (28.24).  Apply
`isQuittingSureExitSet_insert_or_oldLeave_or_otherJoin` to this strict join.
It returns the three displayed alternatives.  In its failed-sure-exit branch
the leaving witness is an old member of `T`, not the anchored entrant `d`,
and every joining witness lies outside `P`.  The checked sure-exit consumer
proves item 1.  QED.

This proposition uses the punishment value only to enter a checked player-
deletion obstruction; it does not assume join antitonicity or an attained
punishment plan.  The witness coalition ranges over the seven nonempty
subsets of `I\{d}`, so the output is finite and relabeling-invariant.  No
iteration or cycle conclusion is asserted.

## 29. Whole-chamber deletion by Nash reselection

The preceding adapters retained or locally repaired the original free-player
profile.  For a chamber-wide reduction this is unnecessary.  After selecting
the paid base member, reselect an exact Nash equilibrium of the complete
base-deleted binary game.

Keep `I={c,d,x,y}`, let `B={c,d}`, `F={x,y}`, and suppose the large-base gap
has selected `c` with its original `gamma`-paid leave, either at a pure cell
or at the unique mixed cell of Proposition 26.1.  For the base-deleted square
put

```text
D_ij={d} union ({x} if i=1) union ({y} if j=1),
R_ij=D_ij\{d},

bar_alpha_j=r_(D_1j)(x)-r_(D_0j)(x),
bar_beta_i =r_(D_i1)(y)-r_(D_i0)(y),                (29.1)

J_c^ij=r_(D_ij union {c})(c)-r_(D_ij)(c),           (29.2)

k_d^ij =
  if R_ij=empty then chi_d-r_d(d)
  else r_(R_ij)(d)-r_(D_ij)(d).                     (29.3)
```

Thus `J_c^ij` is the deleted player's outsider join excess, and `k_d^ij` is
the retained sure owner's Continue-minus-Quit floor excess.

### Proposition 29.1 (complete large-base deletion capstone)

Under a four-player terminal exploitability witness, every large-base `G`
residual has the following exact finite output, while retaining its original
paid label `c` and margin `gamma`.

1. **Deleted pure Nash cell.**  There are `i,j in {0,1}` satisfying

   ```text
   i=0 -> bar_alpha_j<=0,       i=1 -> bar_alpha_j>=0,
   j=0 -> bar_beta_i <=0,       j=1 -> bar_beta_i >=0, (29.4)
   ```

   and

   ```text
   J_c^ij>0       or       k_d^ij>0.                 (29.5)
   ```

2. **Deleted strict matching-pennies cell.**  The deleted differences have
   no pure Nash cell and obey exactly one of

   ```text
   bar_alpha_0>0>bar_alpha_1,
     bar_beta_1>0>bar_beta_0,

   bar_alpha_1>0>bar_alpha_0,
     bar_beta_0>0>bar_beta_1.                        (29.6)
   ```

   Put

   ```text
   Dbar=(bar_alpha_0-bar_alpha_1)
          (bar_beta_1-bar_beta_0)>0,

   Wbar_00=-bar_beta_1 bar_alpha_1,
   Wbar_10= bar_beta_0 bar_alpha_1,
   Wbar_01= bar_beta_1 bar_alpha_0,
   Wbar_11=-bar_beta_0 bar_alpha_0,                  (29.7)

   Jbar_c=sum_(i,j) Wbar_ij J_c^ij,
   Kbar_d=sum_(i,j) Wbar_ij k_d^ij.                  (29.8)
   ```

   Then

   ```text
   Jbar_c>0       or       Kbar_d>0.                 (29.9)
   ```

Conversely, if a selected deleted Nash cell in item 1 has both quantities
nonpositive, or the unique deleted mixed cell in item 2 has
`Jbar_c<=0` and `Kbar_d<=0`, the root at which `d` Quits surely, `x,y` use
that deleted-game Nash profile, and `c` Continues is accepted by
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`.  Its checked
consumer supplies a uniform-equilibrium payoff against unrestricted
behavioral deviations.

Thus Proposition 29.1 eliminates the **entire** large-base `G` chamber into
eight pure polynomial/punishment cells or two strict matching-pennies cells
with the two cleared numerators (29.8).  It has no retained-profile
reprojection condition.

#### Proof

The game on `{x,y}` with persistent base `{d}` is a finite two-player binary
game, so it has a Nash equilibrium.  If it has a pure Nash cell, choose one.
The pure best-response conditions are exactly (29.4).  At the corresponding
singleton-base root, `c` is the sole outsider.  Its Quit-minus-Continue
endpoint difference is exactly `J_c^ij`; the owner-floor excess is exactly
`k_d^ij`.  If both are nonpositive, the checked singleton-base constructor
and consumer apply.  The terminal witness excludes that conclusion, proving
(29.5).

Suppose instead that the deleted game has no pure Nash cell.  The complete
two-by-two classification used in Proposition 26.1 excludes every equality
face and gives exactly (29.6).  Its unique equilibrium is fully mixed, with
positive product-weight numerators (29.7), sum `Dbar`, and rates

```text
Pr(x Quits)=-bar_beta_0/(bar_beta_1-bar_beta_0),
Pr(y Quits)= bar_alpha_0/(bar_alpha_0-bar_alpha_1).  (29.10)
```

The normalized outsider endpoint difference is `Jbar_c/Dbar`, and the
normalized owner-floor excess is `Kbar_d/Dbar`.  If both cleared numerators
are nonpositive, the same singleton-base constructor applies.  Since
`Dbar>0`, the terminal witness therefore forces (29.9).  QED.

### Exact role of the original paid source

The original large-base gap is used only to select a labelled base member
`c`, with either

```text
ell_c^ij>=gamma
```

at an original pure Nash cell or

```text
N_c>=gamma D
```

at the original strict mixed cell.  Proposition 29.1 retains this source
certificate but does not claim that its old free profile survives deletion.
The new deleted-game Nash profile may be completely different.  The price of
that freedom is the compact capstone (29.5)/(29.9): the previously paid
player must now want to rejoin, or the retained owner must want to leave, at
the newly selected exact Nash profile.

This chamber-wide reduction supersedes the reprojection seams `R_x,R_y` as a
classification of large-base `G`; Propositions 26.2 and 28.1 remain stronger
local adapters when the old profile or its two-label repair is useful.  The
new result does not consume the positive numerators in (29.5) or (29.9), and
does not claim that a pure cell extracted from a positive mixed numerator is
itself Nash.

### Proposition 29.2 (paid-boundary singleton-owner capstone)

The two residual coordinates in Proposition 29.1 can be combined by making
the paid player `c` free rather than an outsider.  Let

```text
F'={c,x,y}
```

and consider the complete binary game of these three players with persistent
singleton base `{d}`.  Under the four-player terminal exploitability witness
there is a constant `delta>0` such that every exact Nash point `q` of this
three-player induced game satisfies

```text
quittingSingletonBaseOwnerFloorExcess(reward,d,root(q))>=delta. (29.11)
```

At the same time, the original large-base source supplies a boundary point
`p` on the face where `c` Quits surely such that:

```text
* x,y are exact best responses on that face;
* c's Quit-minus-Continue endpoint difference is at most -gamma. (29.12)
```

Thus the entire large-base `G` chamber reduces to one compact capstone:

```text
a singleton-owner three-free-player binary game whose owner-floor excess
is uniformly positive on its full Nash set, together with a labelled
boundary-face Nash point having a gamma-paid outward defect.              (29.13)
```

Any compiler or impossibility theorem for (29.13) consumes the large-base
arm.  Unlike Proposition 29.1, this formulation has no outsider join
residual and no selected deleted-game Nash profile.

#### Proof

The full induced binary game on `F'` has a nonempty compact Nash set.  At any
Nash point `q`, all three free-player endpoint conditions hold exactly and
there are no outsider labels: `I={d} union F'`.  If the owner-floor excess
were nonpositive at some `q`, then
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` and
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` would give a
uniform-equilibrium payoff against unrestricted behavioral deviations.  The
terminal witness excludes this, so the continuous owner-floor excess is
strictly positive at every point of the compact Nash set.  It therefore has
a positive minimum `delta`, proving (29.11).  Equivalently, this is the
no-outsider specialization of
`exists_uniformPayoff_or_singletonBase_pos_gap`.

For (29.12), use the original paid output of Proposition 26.1.  If it is a
pure cell, let `p` be that pure `{x,y}` point; if it is mixed, use its unique
interior `{x,y}` point.  In either case `x,y` are Nash while both `c,d` Quit
surely.  In the enlarged game with base `{d}`, this is exactly the boundary
face `Pr(c Quits)=1`.  The expected endpoint difference of `c` is

```text
E_p[r_({c,d} union R)(c)-r_({d} union R)(c)]
 = - E_p[ell_c(R)] <= -gamma,                        (29.14)
```

by the paid leave certificate.  This proves (29.12) and the capstone.

The positive gap `delta` is not asserted to be `gamma` or any explicit
function of it.  The theorem aligns the two facts in one finite binary game:
`gamma` controls one labelled boundary face, while compactness controls the
owner floor on the full Nash set.  Producing a path between them, or proving
that no such capstone exists, is the remaining substantive problem.

## 30. The capstone needs the terminal-witness exclusions

Proposition 29.2 deliberately retains a terminal exploitability witness.
The following exact rational table shows why it cannot be replaced by a
purely topological assertion about the Nash carrier and the two displayed
scalar gaps.

Let the players be `I={d,c,x,y}`.  For every nonempty coalition `S`, define

```text
r_S(x)=1 if x in S, and 0 otherwise,
r_S(c)=1 if c notin S, and 0 otherwise,
r_S(y)=1 if y notin S, and 0 otherwise,
r_S(d)=1 if d notin S, and 0 otherwise.              (30.1)
```

All entries are rational and lie in `{0,1}`.

### Proposition 30.1 (exact scalar-capstone independence regression)

For the singleton base `{d}` and free set `{c,x,y}` the table (30.1) has all
of the following properties.

1.  The induced three-player binary game has the unique Nash point

    ```text
    q=(c Continues, x Quits, y Continues).
    ```

    Its owner-floor excess is exactly `1`.

2.  On the face where `c` Quits surely, the unique `x,y` Nash point is

    ```text
    p=(c Quits, x Quits, y Continues),
    ```

    and `c`'s Quit-minus-Continue difference is exactly `-1`.

3.  At the corresponding large base `{c,d}`, both persistent players have
    leave gain `1` at `p`.

4.  There is no empty-base interior simplex solution for **any** active set
    of cardinality at least two.

5.  Nevertheless the game is closed by the checked instant-punishment
    mechanism: player `x` may Quit alone immediately.  Thus this table does
    not carry a terminal exploitability witness.

Consequently, even the conjunction

```text
large-base paid leave
+ positive singleton-owner floor on the full Nash carrier
+ a paid boundary-face outward defect
+ failure of every empty-base interior system
```

does not itself give a contradiction.  A valid closure of Proposition 29.2
must use the terminal-witness exclusions, or some equivalent information
about punishment and joins.  In particular, identifying the owner-floor
functional with the empty-base stationary residual is invalid.

#### Proof

In the induced game with `d` present, `c` strictly prefers Continue, `x`
strictly prefers Quit, and `y` strictly prefers Continue, independently of
the other free actions.  This proves uniqueness of `q`.  At its literal root
the terminal coalition is `{d,x}`.  Player `d` receives `0` when it Quits and
receives `1` after Continuing, because the resulting coalition is `{x}`.
The all-free-Continue event has probability zero, so the punishment-tail
term does not enter; hence

```text
quittingSingletonBaseOwnerFloorExcess(reward,d,root(q))=1.  (30.2)
```

On the face `c=Quit`, the same strict actions of `x,y` give `p`.  Player `c`
receives `0` in `{c,d,x}` and `1` after leaving, in `{d,x}`.  Its endpoint
difference is therefore `-1`.  Player `d` likewise receives `0` in
`{c,d,x}` and `1` after leaving, in `{c,x}`.  This proves items 2--3.

For item 4, consider an alleged empty-base certificate with active set `A`
of cardinality at least two.  If `x in A`, then another active label makes
the opponents' Continue mass for `x` strictly smaller than one.  Forced Quit
always pays `x` exactly `1`, whereas every absorbing coalition produced while
`x` Continues pays it `0`.  Thus

```text
quittingEmptyBaseActiveResidual(reward,root,x)
  =1-quittingStationaryFixedOpponentsContinueMass(root,x)>0,
```

contradicting the active equality.  If `x notin A`, joint absorption is
strictly positive, forced Quit still pays `1`, and the absorbing contribution
while `x` Continues is `0`.  Therefore

```text
quittingEmptyBasePassiveResidual(reward,root,x)
  =1-quittingStationaryContinueMass(root)>0,
```

contradicting the passive inequality.  These two cases exhaust every active
set.

Finally, `r_{\{x\}}(x)=1`; joining `x` also pays every outsider no more than
its payoff from Continuing; and the punishment value of `x` is at most its
solo payoff `1`.  Equivalently,

```text
IsQuittingInstantPunishmentIR reward x,
IsQuittingInstantNoJoin reward x.
```

The checked theorem
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment` therefore
supplies the uniform payoff.  This also explains exactly which hypothesis of
Proposition 29.2 the regression omits.  QED.

### Source and scope

The relevant checked interfaces are
`quittingSingletonBaseOwnerFloorExcess` and
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`PersistentBaseConcreteGap.lean`, the residual definitions and certificate
in `EmptyBaseSemanticDispatch.lean`, and
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment` in
`InstantPunishment.lean`.

This proposition is a boundary falsifier for a scalar/topological proof of
the capstone.  It does **not** satisfy the terminal-witness hypothesis and
does not eliminate the live large-base chamber.  Its useful conclusion is
only that the next closure must retain and exploit the terminal-witness
punishment/join exclusions rather than pass directly from (29.11)--(29.12)
to the empty-base `W` system.

## 31. Normal counterexamples lift to full packet support

The terminal exploitability margin supplies exactly the quantitative input
missing from the scalar regression.  The correct deformation is not a path
between the two Nash carriers in Proposition 29.2.  Instead, constrain every
stationary hazard away from zero, solve the resulting continuous stationary
rate game, and use the terminal gap to prove that all hazards have the same
vanishing order.

Fix a finite player set `I` with `n=|I|>=2`.  Write

```text
s_i=r_{\{i\}}(i),
M=max_(nonempty S,i) |r_S(i)|.
```

Assume every player is punishment-normal:

```text
chi_i<=s_i.                                          (31.1)
```

### Theorem 31.1 (full-support lift from a normal terminal witness)

If the game has a terminal exploitability witness of margin `g>0`, then it
has a normalized singleton source packet `(mu,v)` with

```text
v_i=s_i                    for every i,
mu_i >= 1/C > 0            for every i,              (31.2)

C=1+2M(n-1)/g.
```

In particular the packet has full support.  Equivalently, its mass satisfies

```text
sum_i mu_i=1,
mu_i>0,
sum_j mu_j r_{\{j\}}(i)>=s_i     for every i.        (31.3)
```

The statement is about ordinary independent behavioral quitting.  The
stationary roots below are used only to construct the finite packet; the
terminal gap and the stationary unilateral cap range over unrestricted
behavioral deviations.

#### Step 1: the constrained stationary rate game

Fix `epsilon in (0,1)`.  Identify a stationary marginal with its Quit rate
`q_i in [epsilon,1]`.  Since every rate is positive, the stationary profile
absorbs geometrically and its terminal payoff `V_i(q)` is continuous.

Against fixed opponents put

```text
beta_i = product_(j!=i)(1-q_j),
delta_i=1-beta_i,
Q_i    = payoff from Quit immediately,
A_i    = one-row absorbing contribution while i Continues,
N_i    = A_i/delta_i.                                (31.4)
```

Here `delta_i>0`.  If player `i` uses stationary rate `p`, its terminal payoff
is

```text
V_i(p,q_-i)
 = [p Q_i+(1-p)A_i]/[delta_i+p beta_i].              (31.5)
```

As a function of `p`, (31.5) is fractional linear with derivative of constant
sign.  Its maximizer set on `[epsilon,1]` is therefore `{epsilon}`, `{1}`, or
the whole interval.  The best-response correspondence has nonempty compact
convex values and closed graph.  Kakutani's theorem supplies a constrained
stationary Nash point `q^epsilon`.

Fractional linearity gives the complete support classification

```text
q_i^epsilon=epsilon and Q_i<=N_i,
epsilon<q_i^epsilon<1 and Q_i=N_i,
q_i^epsilon=1 and Q_i>=N_i.                         (31.6)
```

The second and third lines are unrestricted stationary best responses.  By
stationary pure-time extremality they are also unrestricted behavioral best
responses.  In the first line Quit-now is available inside `[epsilon,1]`, so
the only possibly profitable unrestricted response is Never, with gain

```text
N_i-V_i(q^epsilon)
 = epsilon (N_i-Q_i)/(delta_i+epsilon beta_i).       (31.7)
```

#### Step 2: terminal exploitability forces comparable hazards

Apply the terminal exploitability gap to the stationary behavior profile at
`q^epsilon`.  All interior and upper-bound coordinates have zero behavioral
gain.  Therefore some lower-bound coordinate `i` has Never gain at least `g`.  Since
`Q_i,N_i in [-M,M]`, (31.7) gives

```text
delta_i+epsilon beta_i <= 2M epsilon/g.              (31.8)
```

For every `j!=i`, the event that `j` Quits is contained in the event that
some opponent of `i` Quits, so `q_j<=delta_i`.  Together with `q_i=epsilon`,

```text
epsilon <= q_j <= (2M/g)epsilon       for j!=i,
H_epsilon:=sum_j q_j <= C epsilon.                   (31.9)
```

In particular `M>0`, every hazard tends to zero with `epsilon`, and the
normalized direction

```text
mu_i^epsilon=q_i^epsilon/H_epsilon
```

satisfies `mu_i^epsilon>=1/C` for every player.  Choose explicitly any
sequence `epsilon_k downarrow 0`, for example `epsilon_k=1/(k+2)`.  The
normalized directions lie in the compact probability simplex, so pass to a
convergent subsequence of `(mu^{epsilon_k})` and call its limit `mu`.  Then

```text
sum_i mu_i=1,        mu_i>=1/C>0.                    (31.10)
```

#### Step 3: the singleton inequalities

For all sufficiently small `epsilon`, (31.9) rules out the upper line of
(31.6) for every coordinate.  Hence `Q_i<=N_i` for every player.
Equivalently,

```text
delta_i Q_i<=A_i.                                   (31.11)
```

Divide by `H_epsilon` and pass to the selected subsequence.  Because all
hazards vanish,

```text
delta_i/H_epsilon
  -> sum_(j!=i) mu_j,

A_i/H_epsilon
  -> sum_(j!=i) mu_j r_{\{j\}}(i),

Q_i -> r_{\{i\}}(i)=s_i.                            (31.12)
```

The omitted simultaneous-Quit terms are `O(H_epsilon^2)`, so (31.12) is
literal product-law asymptotics, not a correlated approximation.  Taking
limits in (31.11) yields

```text
(sum_(j!=i)mu_j)s_i
 <= sum_(j!=i)mu_j r_{\{j\}}(i).                    (31.13)
```

Adding the equal diagonal term `mu_i s_i` gives (31.3).

Now set `v_i=s_i`.  Equation (31.3) is the packet's singleton-mixture source
inequality.  The solo floor and every positive-mass pin are equalities, while
(31.1) is the punishment floor.  Thus `(mu,v)` is a
`QuittingNormalizedSingletonSourcePacket`.  Its full support is the strict
lower bound (31.10); (31.11) is the finite-`epsilon` inequality used to obtain
the packet source inequality.  QED.

### Corollary 31.2 (support-two is eliminated into full support)

For a normalized singleton source packet on the literal player type `Fin 4`
with support exactly two, either the game already has a uniform-equilibrium
payoff or the same reward table admits a normalized singleton source packet
with support all four players and

```text
normalCore(normalizedSoloMatrix reward)=univ.       (31.13F)
```

Indeed, in the no-uniform branch take the checked terminal exploitability
witness.  The support-two classification first closes the no-harm chamber and
otherwise gives the crossed spectator pattern.  The two supported owners are
punishment-normal by the packet floors and pins.  Each crossed outsider is
also punishment-normal by `abnormal_singletonFloor_chain`; this is the exact
normality argument recorded in reviewed Corollary 17.4.  Theorem 31.1 then
produces the full-support packet.  In the same no-uniform branch, the checked
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` supplies
(31.13F) for the same reward table.

This is a terminating support transition for the maintained question:

```text
support cardinality 2  --->  support cardinality 4. (31.14)
```

For example, the finite-valued complexity `4-card(support)` drops strictly
from `2` to `0`, and Theorem 31.1 is not reapplied at full support.  Hence the
crossed support-two residual cannot return to itself.  The remaining object
belongs to the narrower intersection of the maintained full-support
obligation with full normal core in
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.

### Exact interfaces and nonclaims

The source declarations are
`not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness`,
`quittingStationaryFullRateUnilateralCap`, and
`exists_quitNow_or_never_terminalPayoff_eq_unilateralCap` from
`Quitting/Stationary/BestResponse.lean`, together with
`isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le` from
`Quitting/Stationary/FullRateStationaryVerifier.lean`.  The crossed-outsider
normality input is `abnormal_singletonFloor_chain` from
`Quitting/Classification/AbnormalSingletonConsequences.lean`.  The output
type is exactly `QuittingNormalizedSingletonSourcePacket` from
`Quitting/Classification/ThreePlayer/AnalyticPacket.lean`; no new semantic
compiler is hidden in the construction.  The simultaneous full-normal-core
restriction is the checked
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
`Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`.

The new ordinary mathematics is the constrained-rate Kakutani argument,
the exact regret identity (31.7), the terminal-gap comparator (31.8)--(31.9),
and the resulting full-support packet.  This does not solve the
full-support/full-normal-core case, support three, or the four-player
conjecture.  It does eliminate the support-two obligation without cycling
through another static toggle face.

## 32. A three-core outsider-dominance compiler

For an arbitrary four-player game the recursive LCP normal core is a different
object from packet support and can have cardinality three.  In that case the
omitted player has a strict singleton comparison against every core owner, and
the finite inequalities below give a transparent lift of the unconditional
three-player theorem.  This is not the surviving no-uniform branch of Section
31: the checked theorem
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` already
forces full normal core there.  Section 32 is therefore retained as a
standalone all-behavior adapter, not frontier novelty.

Let `I` be a four-element finite player set, let

```text
M(i,j)=r_{\{j\}}(i)-r_{\{i\}}(i),
C=normalCore(M),
```

and suppose `card(C)=3`.  Write `o` for the unique player outside `C` and
`s_o=r_{\{o\}}(o)`.

### Lemma 32.1 (the removed row is strictly positive on the core)

For every `j in C`,

```text
M(o,j)>0,
```

equivalently

```text
r_{\{j\}}(o)>s_o.                                    (32.1)
```

#### Proof

Suppose instead that `M(o,j)<=0` for some `j in C`.  Every core member belongs
to every `normalLayer(M,n)`.  Inductively, `o` also belongs to every layer:
it belongs to layer zero, and if it belongs to layer `n`, then the distinct
player `j` belongs to that layer and witnesses the nonpositive comparison
required for `o` to belong to layer `n+1`.  Hence `o in normalCore(M)=C`, a
contradiction.  Thus (32.1) is strict.  QED.

### Proposition 32.2 (three-core outsider-dominance compiler)

Assume the following finite inequalities:

```text
s_o<=0,                                                (32.2)

s_o<=r_S(o)       for every nonempty S subset C,       (32.3)

r_{S union \{o\}}(o)<=r_S(o)
                    for every nonempty S subset C.     (32.4)
```

Then the ambient four-player quitting game has a uniform-equilibrium payoff
against unrestricted behavioral deviations.

The singleton instances of (32.3) are automatic and strict by Lemma 32.1.
Thus the genuinely new reward checks in (32.3) concern only core pairs and the
core triple; (32.4) concerns the corresponding join rows.

#### Proof

Restrict the reward table to coalitions contained in `C`.  This is an ordinary
three-player quitting game on the subtype `C`, so
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` supplies a
uniform-equilibrium payoff.  By
`quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`, for
every `epsilon>0` choose a terminal `epsilon`-Nash behavioral profile of the
restricted game.

Extend that profile to the ambient game by making `o` Continue forever.  A
core player's complete behavioral deviation has exactly the same law and
payoff as the corresponding deviation in the restricted game: until
termination the outsider's action is deterministically Continue, and every
terminal coalition remains inside `C`.  Hence every core player retains its
terminal `epsilon`-Nash inequality.

It remains to check an arbitrary complete behavioral deviation by `o`.
Before the first Quit, a one-state quitting-game history consists only of
successive all-Continue outcomes.  Independent behavioral randomization
therefore induces a quit time for `o`, independent of the core players' joint
first-quitter time and coalition.  Couple the deviation with the original
profile on these clocks.  If the core first quits as a nonempty coalition `S`:

* when the core quits before `o`, the payoff remains `r_S(o)`;
* on a tie, the deviating payoff is `r_{S union \{o\}}(o)<=r_S(o)` by (32.4);
* if `o` quits first, its payoff is `s_o<=r_S(o)` by (32.3).

If the core never quits, the original payoff is zero.  A finite quit by `o`
then gives `s_o<=0` by (32.2), while Never still gives zero.  Thus the
deviation is pointwise no better under the coupling.  This covers randomized,
time-dependent, and history-dependent behavioral deviations, not only fixed
quit times.

The lifted profile is consequently terminal `epsilon`-Nash for every
`epsilon>0`.  The target-free checked selector
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
produces one ambient uniform-equilibrium payoff.  QED.

### Corollary 32.3 (exact finite residual at a three-player normal core)

Suppose the ambient game has no uniform-equilibrium payoff and
`card(normalCore(M))=3`.  For its unique outsider `o`, at least one of the
following holds:

```text
(a) 0<s_o;

(b) there is S subset C with 2<=card(S) and r_S(o)<s_o;

(c) there is nonempty S subset C with
        r_S(o)<r_{S union \{o\}}(o).                 (32.5)
```

Indeed, otherwise (32.2)--(32.4) hold and Proposition 32.2 contradicts the
assumed absence of a uniform payoff.  Lemma 32.1 excludes singleton witnesses
from arm (b).  This is a finite relabeling-invariant residual involving only
the outsider's solo, pair, triple, and join rewards.

### Probability, source, and scope audit

The compiler uses the literal restricted reward table on the actual subtype
`C`; it does not infer a support-three packet.  The core profile uses whatever
private behavioral randomization the checked three-player theorem supplies.
The outsider is deterministic Continue.  The deviation comparison is
pathwise after coupling the induced quit times, so no expectation, supremum,
or stopping operation is commuted.

The source declarations are `normalLayer`, `normalCore`, and
`mem_normalLayer_succ` in `Quitting/Classification/LCP/NormalCore.lean`;
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` in
`Quitting/Classification/PlayerReindex.lean`; and the terminal selector in
`Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The two nonsingleton conditions are independently necessary for this
pointwise lift.  If a core coalition `S` Continues at date zero and Quits
surely at date one while `r_S(o)<s_o`, outsider `o` improves by quitting at
date zero.  If `r_{S union \{o\}}(o)>r_S(o)`, it improves by joining a sure
date-zero Quit by `S`.  If the core can Never and `s_o>0`, it improves by
quitting alone.  These tests do not prove that each failed arm is
a counterexample to uniform equilibrium; they show exactly why the present
three-player lift stops there.

Proposition 32.2 closes the complete three-core subchamber satisfying
(32.2)--(32.4).  It does not consume the residual (32.5), the full four-player
normal-core chamber, or the projective-Q-bar path fork.  It is additional
nonsingleton semantic structure, not another subdivision of the already
dispatched static toggle cycle.

## 33. The exact normal-core cardinality waist

This section records a source audit, not new conference mathematics.  The
core-size exclusion is already checked as
`standardQSide_core_card_eq_three_or_four` in
`Quitting/Classification/LCP/StandardQSideExample.lean`.  More strongly, the
entire three-core counterexample branch is already eliminated by
`exists_uniformEquilibriumPayoff_of_normalCore_card_three` in
`Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`.
The calculations below explain the matrix waist but must not be exported or
counted as progress on the maintained singleton-packet question.

Assume `I` has four players and the game has no uniform-equilibrium payoff.
Let

```text
M=normalizedSoloMatrix(r),
C=normalCore(M).
```

The checked theorem `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
gives

```text
C nonempty,
normalPlayerMatrix(M) has no homogeneous simplex solution,
normalPlayerMatrix(M) is Standard-Q.                  (33.1)
```

### Proposition 33.1 (core size is three or four)

Under (33.1),

```text
card(C) in {3,4}.                                     (33.2)
```

#### Proof

The core cannot be a singleton: every member of a stabilized normal core has
a distinct nonpositive blocker in that same core by
`exists_core_blocker_of_mem_normalCore`.

Suppose `C={a,b}`.  The blocker property gives

```text
M(a,b)<=0,      M(b,a)<=0.
```

If either entry were zero, the singleton mass on the opposite column would be
a homogeneous simplex solution of the two-by-two zero-diagonal principal.
Thus absence of a homogeneous solution forces both entries strictly negative.
But the standard LCP with right-hand side `q=(-1,-1)` is then impossible: for
every nonnegative weight `z`, its first residual is

```text
-1+z_b M(a,b)<0.
```

This contradicts Standard-Q.  Since the ambient cardinality is four, only
three and four remain.  QED.

### Proposition 33.2 (the three-core branch is cyclic with positive determinant)

If `card(C)=3`, then after relabeling `C` by `Fin 3`, its principal normalized
matrix has one of the two strict cyclic orientations and

```text
0<cycleDeterminant.                                   (33.3)
```

#### Proof

Let `N=normalPlayerMatrix(M)`.  Its diagonal is zero.  Since `N` has no
homogeneous simplex solution, every owner column has a strictly negative entry
by `exists_negative_entry_in_column_of_noHomogeneous`.  Choose such a harmed
row.  Since `N` is Standard-Q, that row has a strictly positive entry by
`exists_positive_entry_in_row_of_standardQ`.  With exactly three labels, the
positive column is distinct from both the harmed row (zero diagonal) and the
negative owner column.  Hence `N` has internal crossed rows.

`ThreePointCrossedRows.exists_cyclicLabeling_of_card_eq_three` gives a forward
or reverse strict cyclic labeling.  The exact checked determinant tests are
`standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_forward` and
`standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse` in
`Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`.  They identify
Standard-Q plus absence of a homogeneous solution with positivity of the
cycle determinant.  This proves (33.3).  QED.

For project status, this split is superseded by the checked unconditional
three-core elimination theorem named above.  Section 32 remains independently
useful as a transparent all-behavior lift, but it is not needed to eliminate
the normal-core-cardinality-three counterexample branch.

### Proposition 33.3 (the four-core projective waist)

If `card(C)=4`, identify `C` with `I`.  Then `M` itself is Standard-Q and has
no homogeneous simplex solution.  Consequently `M` is projective Q.  Exactly
one of the following holds:

```text
(a) M is projective-Q-bar;

(b) there is a proper principal set S subset I with
      2<=card(S)<=3
    such that principalMatrix(M,S) is not projective Q. (33.4)
```

#### Proof

The equivalence
`isProjectiveQMatrix_iff_standard_or_homogeneous` makes `M` projective Q from
its Standard-Q property.  Split on projective-Q-bar.  If it fails,
`exists_nonprojectivePrincipalMatrix_of_not_projectiveQBar` supplies a nonempty
principal `S` which is not projective Q.  It cannot be all four players because
`M` is projective Q.

It also cannot be a singleton.  A one-by-one zero matrix is projective Q for
every scalar right-hand side `q`: if `q>=0`, put all projective mass on the
cemetery coordinate; if `q<0`, put all mass on the singleton coordinate, so
the residual is zero.  Therefore `2<=card(S)<=3`, proving (33.4).  QED.

For a two-player witness `S={a,b}`, nonprojective Q is equivalent to the exact
mutual-harm signs

```text
M(a,b)<0,       M(b,a)<0.                             (33.5)
```

Indeed, either nonnegative off-diagonal entry gives a homogeneous singleton
solution, hence projective Q; if both are negative, the `q=(-1,-1)` argument
above rules out Standard-Q and there is no homogeneous solution, so the
standard-or-homogeneous equivalence rules out projective Q.

### Status of the waist

The already-checked background alternative is:

```text
three-core:
  checked uniform-equilibrium payoff;

four-core:
  a nonprojective principal of size two or three.
```

Here the projective-Q-bar alternative is already eliminated in the
no-uniform branch by the unconditional checked strategic fork
`quittingPunishmentNormalPathStrategicFork` and its Snell consumer
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`.  Equivalently, the
checked fused counterexample residual already returns
`PunishmentNormalResidualHardClass`.

The displayed proper-principal reduction is relabeling invariant.  It does
**not** by itself define a recursive packet descent: the
principal subset need not carry a normalized singleton packet or an ambient
strategy adapter.  Section 34 supplies an ambient adapter on one exact finite
subchamber.  Outside that subchamber the proper-principal arm still supplies
only explicit outsider reward failures and the returned-block relative-error
obstruction.  This section remains checked background only.

## 34. Small-principal outsider-safety lift

This section addresses the actual four-core residual rather than the already
closed three-core branch.  It uses the proper nonprojective principal selected
by the checked counterexample fusion, but the lift theorem itself needs only a
proper set with two or three players.

Let `I` have four players, let `P` be a proper player set with

```text
card(P) in {2,3},
```

and write `s_o=r_{\{o\}}(o)` for each omitted player `o notin P`.  Assume that
for every such `o` and every nonempty coalition `S subset P`,

```text
s_o <= 0,                                             (34.1)
s_o <= r_S(o),                                        (34.2)
r_{S union {o}}(o) <= r_S(o).                         (34.3)
```

### Proposition 34.1 (small-principal all-behavior lift)

Under (34.1)--(34.3), the ambient four-player quitting game has a
uniform-equilibrium payoff against unrestricted behavioral deviations.

#### Proof

Restrict the reward table literally to coalitions and payoff coordinates in
`P`, using `quittingPrincipalReward reward P`.  If `card(P)=2`, apply
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two`; if
`card(P)=3`, apply
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`.  In either
case the checked implication
`quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff` supplies,
for every positive `epsilon`, a terminal `epsilon`-Nash behavioral profile of
the restricted game.

Extend this profile to `I` by making every player outside `P` Continue
forever.  A player in `P` sees exactly the restricted game.  Every complete
ambient behavioral deviation by that player therefore has the same law and
payoff as its restricted-game deviation, so its terminal gain is at most
`epsilon`.

Fix an omitted player `o` and an arbitrary complete behavioral deviation by
`o`.  All other omitted players still Continue forever.  Couple the deviating
quit time of `o` with the restricted profile's first finite quit time and
coalition `S`.  On every deterministic realization:

```text
core quits before o:   payoff is r_S(o);
o ties the core:       payoff is r_{S union {o}}(o) <= r_S(o);
o quits first:         payoff is s_o <= r_S(o).
```

The last two inequalities are (34.3) and (34.2).  If the restricted profile
Never quits, the prescribed ambient payoff to `o` is zero; quitting at any
finite date gives `s_o<=0` by (34.1), and Never again gives zero.  Thus the
deviation is pointwise no better.  Conditioning and averaging proves the
same inequality for arbitrary randomized, time-dependent behavioral
deviations, including ties and Never.

Hence the extended profile is terminal `epsilon`-Nash for every positive
`epsilon`.  The checked target-free selector
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
gives the ambient uniform-equilibrium payoff.  QED.

### Corollary 34.2 (finite residual on the four-core hard branch)

Assume `card(I)=4` and that the ambient game has no uniform-equilibrium
payoff.  The checked fusion theorem
`exists_fourPlayerCounterexample_fusedResidual` gives full normal core and a
`PunishmentNormalResidualHardClass`.  Apply its checked
`toResidualHardClass` projection.  The resulting full-matrix projective-Q-bar
failure selects a nonempty principal `P` of `normalizedSoloMatrix reward` that
is not projective Q.  The full matrix is itself projective Q because full core
identifies its normal-player matrix, up to the canonical subtype reindexing,
with the checked Standard-Q, nonhomogeneous full matrix.  A singleton
zero-diagonal principal is always projective Q.  Consequently

```text
2 <= card(P) <= 3.                                    (34.4)
```

For at least one omitted player `o notin P`, at least one of the following
finite failures holds:

```text
(a) 0 < s_o;

(b) there is nonempty S subset P with r_S(o) < s_o;

(c) there is nonempty S subset P with
      r_S(o) < r_{S union {o}}(o).                   (34.5)
```

Otherwise every omitted player satisfies (34.1)--(34.3), so Proposition 34.1
contradicts the assumed absence of a uniform payoff.

When `card(P)=2`, nonprojective Q additionally forces the exact mutual-harm
signs on its two off-diagonal singleton entries.  When `card(P)=3`, (34.5)
contains only finitely many singleton, pair, triple, and join comparisons.
Thus (34.4)--(34.5) is a literal finite nonsingleton residual attached to the
proper principal selected by the checked four-player hard class.

### Proposition 34.3 (a hard principal has an outward packet crossing)

Let `packet` be a full-support normalized singleton source packet, and let
`P` be any nonempty proper principal set for which

```text
principalMatrix(normalizedSoloMatrix reward,P)
```

has no homogeneous simplex solution.  Then there are

```text
harmed in P, owner in P, helper notin P
```

such that

```text
M(harmed,owner)<0<M(harmed,helper).                 (34.6)
```

In particular every nonprojective principal selected in Corollary 34.2 has a
strict singleton crossing that exits that principal.

#### Proof

Write `mu` for the packet mass.  Full support gives `mu_j>0` for every player,
and the packet pins its target to every solo payoff.  Hence singleton-mixture
feasibility is exactly

```text
sum_j mu_j M(i,j) >= 0                              (34.7)
```

for every row `i`.

If the internal sum

```text
sum_{j in P} mu_j M(i,j)
```

were nonnegative for every `i in P`, normalize the positive restricted mass
by `sum_{j in P}mu_j`.  This would be a homogeneous simplex solution of the
principal matrix, contrary to hypothesis.  Thus some `harmed in P` has
strictly negative internal sum.  Since every restricted mass is positive,
some `owner in P` has `M(harmed,owner)<0`.

Splitting (34.7) into its internal and external parts shows that the external
sum is strictly positive.  Again all masses are positive, so some
`helper notin P` has `M(harmed,helper)>0`.  The strict signs and zero diagonal
make the three roles pairwise distinct, proving (34.6).  A nonprojective-Q
matrix has no homogeneous simplex solution by
`isProjectiveQMatrix_iff_standard_or_homogeneous`, so the last assertion
follows.  QED.

### Corollary 34.4 (the surviving Section 31 intersection)

Start from the nonuniform branch of Corollary 31.2.  Then the same reward
table has simultaneously:

```text
* a normalized singleton source packet with support univ;
* normalCore(normalizedSoloMatrix reward)=univ;
* a proper nonprojective principal P with 2<=card(P)<=3;
* one outsider failure from (34.5); and
* an outward packet crossing (34.6) for that same P.
```

The first two items are Corollary 31.2.  The checked counterexample fusion and
`PunishmentNormalResidualHardClass.toResidualHardClass` give the third.
Proposition 34.1 forces the fourth, since otherwise its all-behavior lift would
contradict nonuniformity.  The full-support packet and nonprojectivity of `P`
meet Proposition 34.3 and give the fifth.

This is the precise live object retained below.  Propositions 34.1 and 34.3
were stated more generally only to separate their proofs; no claim is made
that arbitrary full-support packets, without full normal core and the hard
principal, are the maintained frontier.

### Probability, source, and scope audit

The restricted game is played on the actual subtype `P`; no packet or
principal-game punishment value is inferred.  Outsiders Continue
deterministically.  The all-behavior comparison is pathwise in the two quit
times and the restricted first-quitter coalition before taking expectations.
It therefore covers arbitrary behavioral stopping laws, ties, and Never.

The source declarations are `quittingPrincipalReward` in
`Quitting/Classification/LCP/PrincipalReward.lean`, the two small-player
existence theorems in `Quitting/Classification/PlayerReindex.lean`, the
target-free terminal selector in
`Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`, and the
four-player fused hard-class theorem in
`Research/Quitting/FourPlayerCounterexampleFusion.lean`.

The lift closes the entire outsider-safe subchamber for every selected proper
principal of size two or three, and Proposition 34.3 localizes an outward
packet crossing on every remaining hard principal.  It does not consume the
three failure arms in (34.5), prove that restriction preserves ambient
punishment values, turn the localized crossing into an all-behavior compiler,
or turn a nonprojective principal into a smaller normalized singleton packet.
Accordingly this is a compiler-valued finite narrowing of the live four-core
hard branch, not a recursive proof of the four-player conjecture.

## 35. Support three promotes completely to full support

The reviewed normal terminal-gap lift in Theorem 31.1 composes with the
checked four-player full-normal-core theorem more strongly than the maintained
question currently records.  In fact a support-three packet cannot retain an
abnormal outsider in the terminal-witness branch: abnormality makes every
off-diagonal entry in that outsider's normalized singleton row strictly
positive, while full normal core requires a distinct nonpositive entry.

Let `I=Fin 4`, let

```text
witness : QuittingTerminalExploitabilityWitness reward
packet  : QuittingNormalizedSingletonSourcePacket reward,
card(packet.support)=3.
```

Put

```text
g = witness.terminalGap,
M = max_(nonempty S,i) |r_S(i)|,
C = 1+2M(4-1)/g.
```

### Theorem 35.1 (support-three full-support promotion)

There is a normalized singleton source packet `packet'` for the same reward
table such that

```text
packet'.support=univ,
packet'.mass(i)>=1/C>0 for every i.                  (35.1)
```

Consequently the finite complexity

```text
4-card(packet.support)
```

drops from `1` to `0`.  Both the outsider-crossing arm and the internal cyclic
screen are eliminated as independent support-three obligations.

#### Proof

The terminal-gap field of `witness` rules out a uniform-equilibrium payoff.
The checked theorem

```text
normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
```

therefore gives

```text
normalCore(normalizedSoloMatrix reward)=univ.        (35.2)
```

Let `o` be the unique player outside `packet.support`.  Every supported player
`j` has positive packet mass and hence is punishment-normal by
`QuittingNormalizedSingletonSourcePacket.isQuittingNormalPlayer_of_mass_pos`.
Suppose for contradiction that `o` is not punishment-normal.  Then `o` is
abnormal, so for every supported `j` the checked
`abnormal_singletonFloor_chain` gives

```text
r_{\{o\}}(o) < quittingPunishmentValue(reward,o)
             <= r_{\{j\}}(o).                       (35.3)
```

Thus

```text
normalizedSoloMatrix reward o j > 0                 (35.4)
```

for every `j` in the three-player support.  But (35.2) and
`exists_core_blocker_of_mem_normalCore` supply a player `k!=o` with

```text
normalizedSoloMatrix reward o k <= 0.               (35.5)
```

Since `o` is the unique outsider, `k` belongs to `packet.support`; (35.4) and
(35.5) contradict one another.  Hence `o` is punishment-normal.  All four
players therefore satisfy

```text
quittingPunishmentValue reward i <= r_{\{i\}}(i).   (35.6)
```

The witness supplies the unrestricted behavioral terminal gap `g>0` required
by Theorem 31.1.  Applying that theorem to (35.6) gives a probability vector
`mu` with `mu_i>=1/C>0` and

```text
sum_j mu_j r_{\{j\}}(i) >= r_{\{i\}}(i)             (35.7)
```

for every player.  With target equal to the own-singleton payoff vector,
(35.6)--(35.7) are precisely the punishment-floor and mixture fields of a
normalized singleton source packet; the solo fields and all pins are
equalities.  Strict positivity of every mass coordinate makes its support
`univ`, proving (35.1).  QED.

### Corollary 35.2 (support-three chamber elimination)

Suppose the analytic waist returns a four-player packet of support three.
Then either the game has a uniform-equilibrium payoff or the same reward table
has a full-support normalized singleton packet.  Thus the exact support-three
frontier makes the terminating transition

```text
support cardinality 3  --->  support cardinality 4. (35.8)
```

There is no remaining unique-outsider-crossing or cyclic-determinant chamber
at support three.  Those signs may still occur as intermediate data, but they
are bypassed by the full-support promotion.

### Subsumption and source audit

This is a composition theorem, but it is not already one of its inputs.

* `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
  `Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`
  supplies (35.2), but says nothing about packet support or punishment
  normality.  The row contradiction (35.3)--(35.5) is the connector.
* `supportThree_allNormal_or_cyclicSignScreen` stops at **all
  punishment-normal** or the internal cyclic screen.  The present proof is
  stronger in the terminal-witness branch because full normal core rules out
  its abnormal-outsider premise before the sign screen is needed.
* Theorem 31.1 produces a full-support packet from an all-normal terminal
  witness, but it does not prove that a three-supported packet's fourth player
  is normal.  Its proof and
  unrestricted-deviation audit were independently reviewed in
  `feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_31.md`.
* The nearby checked `exists_quantitative_normalTerminalGap_root` and
  `exists_fullSupport_normalizedSingletonSourcePacket_of_vanishingRoots`
  expose the two halves of the same route.  The first declaration does not
  retain in its result type the `O(epsilon)` total-hazard upper bound needed
  to instantiate the second declaration's `Tendsto ... 0` input.  They do
  not, as currently typed, subsume Theorem 31.1 or this corollary.
* `exists_uniformEquilibriumPayoff_of_normalCore_card_three` is about a
  three-element recursive normal core.  Here the recursive normal core has
  cardinality four; the packet support has cardinality three.  Thus that
  theorem does not subsume (35.1).
* No heredity of Standard-Q or projective Q-bar is used.  In particular the
  proof does not make the invalid inference that the packet's three-player
  principal inherits the ambient Standard-Q property.

The probability semantics of (35.1) are exactly those of Theorem 31.1:
the constrained stationary roots are product roots, while their unilateral
caps range over all behavioral stopping laws, including finite quit times and
Never.  The preliminary row contradiction is entirely static and uses literal
singleton rewards and the checked behavioral punishment value.

The theorem does **not** consume the resulting full-support chamber.  It also
does not identify packet support with the recursive normal core: their
different cardinalities are essential to the contradiction.  Its strict
gain is exact: support three is removed from the maintained four-player packet
frontier and replaced by a literal full-support packet on the same reward
table.

## 36. The full normal core is punishment-normal: all proper packet supports disappear

Section 35 used only one outsider row.  The same argument is actually a
general connector between the repository's two notions of normality.

### Lemma 36.1 (recursive-core membership implies punishment normality)

Let `I` be any finite player set.  For every quitting reward table and every
player `i`,

```text
i in normalCore(normalizedSoloMatrix reward)
  -> IsQuittingNormalPlayer reward i.                (36.1)
```

#### Proof

Write `M=normalizedSoloMatrix reward` and suppose `i` belongs to its normal
core.  The checked `exists_core_blocker_of_mem_normalCore` supplies `j!=i`
such that

```text
M(i,j)<=0.                                           (36.2)
```

By `normalizedSoloMatrix_eq_soloReward_sub`, this is

```text
quittingSoloReward reward j i
  <= quittingSoloReward reward i i.                 (36.3)
```

If `i` were not punishment-normal, it would be abnormal.  The checked
`abnormal_singletonFloor_chain reward` applied to `j!=i` gives

```text
quittingSoloReward reward i i
  < quittingPunishmentValue reward i
  <= quittingSoloReward reward j i,                 (36.4)
```

contradicting (36.3).  Hence `i` is punishment-normal.  QED.

Equivalently,

```text
normalCore(normalizedSoloMatrix reward)
  subset punishmentNormalPlayers reward.            (36.5)
```

This inclusion is one-way; no converse is asserted.

### Theorem 36.2 (four-player counterexample branch has a full-support packet)

Let `I=Fin 4` and let

```text
witness : QuittingTerminalExploitabilityWitness reward.
```

With

```text
g = witness.terminalGap,
M = max_(nonempty S,i) |r_S(i)|,
C = 1+2M(4-1)/g,
```

there exists a normalized singleton source packet `packet` for the same
reward table satisfying

```text
packet.support=univ,
packet.mass(i)>=1/C>0       for every i.             (36.6)
```

#### Proof

The terminal-gap witness excludes every uniform-equilibrium payoff.  The
checked four-player theorem

```text
normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
```

therefore gives

```text
normalCore(normalizedSoloMatrix reward)=univ.        (36.7)
```

Lemma 36.1 turns (36.7) into punishment normality of every player.  Theorem
31.1 now applies directly to the witness's unrestricted behavioral terminal
gap and gives (36.6).  QED.

### Corollary 36.3 (the four-player analytic waist needs only full support)

For every four-player quitting reward table, at least one of the following
two alternatives is available:

```text
there is a uniform-equilibrium payoff,
or
there is a full-support normalized singleton source packet. (36.8)
```

Indeed, apply the checked analytic waist.  Its uniform-payoff output is the
first branch.  In the packet branch, if a uniform payoff exists we are again
done; otherwise choose the checked terminal witness and apply Theorem 36.2.
The newly produced packet is independent of the support of the packet first
returned by the waist.

Thus all proper packet supports terminate at once in the no-uniform branch:

```text
support 1, 2, or 3  --->  support 4.                 (36.9)
```

In particular Sections 31 and 35 are strict special cases of Theorem 36.2 as
frontier transitions, although their local constructions and quantitative
audits remain valid.

### Subsumption audit and exact frontier effect

The connector (36.1) was not found by a narrow search in the normal-core,
abnormal-player, packet, or LCP source subtrees.

* `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
  ends at recursive-core equality.  It does not state behavioral punishment
  normality.
* `abnormal_singletonFloor_chain` gives (36.4) but does not mention the
  recursive core.  The distinct nonpositive core blocker is the missing
  opposing inequality.
* The checked card-three normal-core theorem is neither used nor applicable:
  (36.7) is a four-element core.
* `supportThree_allNormal_or_cyclicSignScreen` and the crossed support-two
  machinery become unnecessary for the **existence of a full-support packet**
  under a four-player terminal witness.  They retain value as local finite
  descriptions, but no longer define separate packet-support obligations.
* The nearby checked normal-terminal-gap root theorem still omits its
  `O(epsilon)` total-hazard estimate from the existential result type.  The
  independently reviewed Theorem 31.1 remains the source of the final
  full-support packet and its explicit `1/C` floor.

The result also explains the scope of the existing full-support sign
falsifier.  Its row with no distinct nonpositive entry prevents full normal
core, so it cannot inhabit (36.7).  Conversely, the paired-singleton
residual-hard matrix has full normal core and every player is punishment
normal, fully consistent with Lemma 36.1; its checked period-two uniform
payoff shows that (36.6) is a frontier reduction, not a contradiction.

All unrestricted-deviation semantics enter through the terminal witness and
Theorem 31.1.  Lemma 36.1 itself is a literal singleton-reward and behavioral
punishment-value comparison.  No stationary-strategy completeness, inherited
principal Standard-Q property, or packet/core identification is used.

The exact remaining four-player packet obligation is therefore the
full-support chamber, intersected in a hypothetical counterexample with the
already checked full normal core and punishment-normal residual-hard data.
This theorem does not consume that chamber or prove the four-player
conjecture.

## 37. A four-player counterexample has a two- or three-player nonprojective principal face

Section 36 leaves a full-support/full-core packet.  The checked projective
Q-bar consumer and the full-core LCP restriction force one further finite
matrix alternative on the same reward table.

### Theorem 37.1 (proper-principal cardinality dispatch)

Let `I=Fin 4` and let

```text
witness : QuittingTerminalExploitabilityWitness reward.
```

Write `M=normalizedSoloMatrix reward`.  Then there is a finite player set
`K subset I` such that

```text
K.card=2 or K.card=3,                                (37.1)
not IsProjectiveQMatrix(principalMatrix M K).        (37.2)
```

For the same reward table there is also the quantitative full-support packet
of Theorem 36.2, the normal core of `M` is `univ`, and every player is
punishment-normal.

#### Proof

The witness excludes a uniform-equilibrium payoff.  If `M` were projective
Q-bar, the checked all-behavior Snell consumer

```text
exists_uniformEquilibriumPayoff_of_projectiveQBar_snell
```

would give such a payoff.  Hence `M` is not projective Q-bar.  Expanding the
definition gives a nonempty `K` satisfying (37.2).

The checked theorem

```text
projectiveQ_of_not_exists_uniformEquilibriumPayoff
```

says that the normalized matrix on the recursive normal core is projective
Q.  The checked four-player full-core theorem says that this core is `univ`.
After the canonical subtype reindexing, the full ambient matrix `M` is
therefore projective Q.  Consequently the witness `K` in (37.2) cannot be
`univ`, so

```text
K.card<4.                                             (37.3)
```

Nor can `K` be a singleton.  If `K={i}`, its principal matrix has its unique
entry

```text
M(i,i)=0
```

by `normalizedSoloMatrix_diagonal`.  For every projective right-hand side,
the cemetery-zero, singleton-mass-one vector is a projective LCP solution:
its total mass is one and every residual and complementary product is zero.
Thus every singleton principal is projective Q, contradicting (37.2).

Since `K` is a nonempty subset of a four-element set, exclusion of cardinality
one and four leaves exactly (37.1).  The packet, full-core, and all-normal
claims are Theorem 36.2 and Lemma 36.1 for the same witness and reward table.
QED.

### Corollary 37.2 (strengthened analytic waist)

Every quitting game on `Fin 4` has at least one of the following outputs:

```text
a uniform-equilibrium payoff,
or
a full-support normalized singleton packet together with
a nonprojective normalized-solo principal face of size two or three. (37.4)
```

On the second branch the same table also has full normal core and every player
is punishment-normal.  Thus the support-complexity reduction of Section 36
lands in a finite proper-principal alternative, rather than only in an
unstructured full-support matrix chamber.

### Boundary and source audit

The exact paired-singleton matrix

```text
[[ 0, 3,-1,-1],
 [ 3, 0,-1,-1],
 [-1,-1, 0, 3],
 [-1,-1, 3, 0]]
```

is the sharp size-two test.  The checked
`pairedSingletonMatrix_not_projectiveQBar` proof uses the cross pair `{0,2}`
and shows directly that its principal block is not projective Q.  The same
matrix has full normal core and is standard Q.  Its checked period-two payoff
also shows why (37.1)--(37.2) are a residual classification, not a
contradiction or a terminal-gap example.

The singleton exclusion is sharp at the opposite boundary: zero diagonal
alone supplies a homogeneous cemetery-zero projective solution on every
one-player face, independently of all off-diagonal rewards.

A narrow source search found the following nearby checked results.

* `PunishmentNormalResidualHardClass.exists_ambient_allNormal_nonprojectivePrincipal`
  already exposes a nonempty all-normal nonprojective principal, but gives no
  `Fin 4` cardinality reduction.
* `projectiveQ_of_not_exists_uniformEquilibriumPayoff` proves projective Q only
  on the recursive normal-core matrix.  Full-core identification is required
  to exclude the four-player principal witness.
* `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` closes the full
  projective-Q-bar branch against unrestricted behavioral deviations, but
  does not select the failing principal when Q-bar is false.
* No declaration matching a nonprojective-principal cardinality `2 or 3` was
  found in the LCP or singleton-packet source subtrees.

The theorem is finite matrix structure, not a new behavioral compiler.  Its
all-behavior content is exactly the checked Snell exclusion of the
projective-Q-bar branch and the terminal-witness/full-support construction
already audited in Sections 31 and 36.  It does not prove that either the
size-two or size-three nonprojective face inherits packet mass, is itself a
quitting subgame counterexample, or enters the existing support-two or
support-three packet compilers.  Those are the next adapter questions.

## 38. The full packet and the canonical tight face share a crossed row

The maintained full-support packet and the canonical positive-debt dynamic
tail are selected independently in the checked fusion theorem.  There is
nevertheless one exact finite connector between them.  Either the tail has a
proper limiting tight-owner face, which is a genuine decrease of the actual
late active-player set, or one packet row with positive surplus is forced to
carry a negative coordinate of the tail's strict separator.

Keep `I=Fin 4` and a terminal exploitability witness `witness`.  Let `packet`
be the quantitative full-support packet of Theorem 36.2, and let

```text
seam : QuittingPositiveDebtDynamicTailWitness witness
```

be any canonical positive-debt tail.  Write

```text
T = seam.tightOwnerFinset,
s_i = r({i})_i,
u_i = quittingSingletonMixture reward packet.mass i,
e_i = u_i-s_i.
```

Full packet support and pinning give

```text
packet.target i=s_i,       e_i>=0                    (38.1)
```

for every `i`.  The checked dynamic-tail theorem gives

```text
eventually every active root owner belongs to T.      (38.2)
```

### Theorem 38.1 (tight-face/negative-surplus alternative)

At least one of the following holds.

1. **Proper actual tight face.**  `T != univ`.  Consequently every
   sufficiently late exact root of the canonical tail is supported on one
   fixed proper subset of `Fin 4`.

2. **Separator-anchored crossed packet row.**  There are a covector `p`, a
   margin `m>0`, and three pairwise distinct players `i,j,k` such that

   ```text
   sum_l p_l^2 + m^2 = 1,
   p_i<0,
   m/4 <= (-p_i)*e_i,
   m/4 <= e_i,
   m/4 <= normalizedSoloMatrix reward i j,
   normalizedSoloMatrix reward i k <= 0.             (38.3)
   ```

   Thus the same coordinate `i` is simultaneously a quantitatively strict
   positive packet-surplus row, a negative coordinate of the actual tail
   separator, and a full-normal-core crossed row.

#### Proof

If `T!=univ`, (38.2) is exactly
`QuittingPositiveDebtDynamicTailWitness.eventually_active_mem_tightOwnerFinset`,
so the first alternative holds.

Assume `T=univ`.  Apply

```text
seam.exists_strictCovector_on_tightOwners_of_no_uniformPayoff
```

to `witness.not_exists_uniformEquilibriumPayoff`.  It supplies `p,m` with
`m>0`, the normalization in (38.3), and, for every tight owner `a`,

```text
m <= p dot (seam.limit.value-r({a})).                 (38.4)
```

Because every owner is tight, the definition of `T` gives

```text
seam.limit.value=s.                                   (38.5)
```

Multiply (38.4) by the nonnegative packet mass of `a` and sum over all four
owners.  The masses sum to one, so

```text
m
 <= p dot (s-sum_a packet.mass(a) r({a}))
  = p dot (s-u)
  = sum_l (-p_l)e_l.                                  (38.6)
```

There are four coordinates.  Hence some `i` satisfies

```text
m/4 <= (-p_i)e_i.                                     (38.7)
```

Since `e_i>=0` and `m>0`, (38.7) forces `p_i<0` and `e_i>0`.  The separator
normalization gives `|p_i|<=1`, so (38.7) also gives `m/4<=e_i`.

Packet pinning rewrites the surplus as

```text
e_i
 = sum_a packet.mass(a)
     * normalizedSoloMatrix reward i a.               (38.8)
```

The diagonal summand is zero.  Since the remaining packet masses are
nonnegative and sum to `1-packet.mass(i)<1`, finite averaging in (38.8)
selects some `j!=i` with

```text
e_i <= normalizedSoloMatrix reward i j.               (38.9)
```

In particular the last quantity is at least `m/4>0`.

The checked four-player counterexample theorem gives

```text
normalCore(normalizedSoloMatrix reward)=univ.
```

Applying `exists_core_blocker_of_mem_normalCore` to `i` selects `k!=i` with

```text
normalizedSoloMatrix reward i k<=0.                   (38.10)
```

The strict signs in (38.9)--(38.10) force `j!=k`.  This proves (38.3).  QED.

### Source and subsumption audit

The ingredients were inspected in:

* `NormalTerminalGapConstrainedStationary.lean`, for the same-table
  full-support packet and full normal core;
* `StrictCovectorDynamicTail.lean`, for the canonical tail, the limiting
  tight-owner separator, and eventual containment of every active owner in
  the tight face; and
* `NormalCore.lean`, for `exists_core_blocker_of_mem_normalCore`.

The checked synthesis
`exists_fourPlayerCounterexample_fusedResidual` stores a packet, a strict
covector tail, and full normal core simultaneously, but does not relate the
packet mass to the tail separator.  A narrow phrase and symbol search found
no packet/tight-owner or packet/strict-covector connector.  Equation (38.6)
is the new step.

This is not another singleton/LCP classification: its first branch is a
proper **actual late root-support** restriction, and its second branch ties a
literal tail-separator coordinate to a packet surplus.  It does not yet feed
either branch into an unrestricted-behavior compiler.  In particular, the
proper tight face is not automatically an ambient lower-player game, and the
crossed row in (38.3) does not identify any nonsingleton collision payoff.
The next exact question is whether the negative separator coordinate `i` and
its quantitatively positive owner `j` force a pair/triple toggle accepted by
an existing stationary or collision compiler.
