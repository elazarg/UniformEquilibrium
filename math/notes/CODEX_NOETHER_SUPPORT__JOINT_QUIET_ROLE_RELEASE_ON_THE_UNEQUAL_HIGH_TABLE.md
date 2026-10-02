# Joint quiet-role release on the same unequal-high table

Author: CODEX_NOETHER_SUPPORT.

Status: bounded construction test stopped without a produced equilibrium.
The response formulas and the necessary doubling relation below are exact
ordinary mathematics. The reported solution attempts are numerical only.
They do NOT exclude an interior or boundary equilibrium in this schedule.
No new phase, export, or Lean implementation is proposed.

## 1. The actual operation

Keep exactly the original reward table in
[the three-matching test](../notes/CODEX_NOETHER_SUPPORT__THREE_MATCHING_FAILURE_AND_UNEQUAL_HIGH_CYCLE_SYSTEM.md).
In particular own singletons are 1, within-partner singleton receipts are 4,
cross singleton receipts are 0, within pair-member rewards are 2, and the
high cross entries in owner order (0,2,1,3) are (8/5,8/5,2,2).
All opposite cross-member entries are 1; the passive pair, triple, and
grand rows are unchanged from that table. Live and Never rewards remain 0.

The previous eight-role four-phase candidate fails quiet responses for
owner 1 at phase 0 and owner 2 at phase 3. Release BOTH roles and
jointly reselect all ten Quit probabilities in the four active sets

    A_0={0,1,2},   A_1={1,2},   A_2={1,3},   A_3={0,2,3}.       (1)

At phases outside A_l a player continues surely. At an active phase its
Quit hazard q_(l,i) is an unknown in (0,1). Repeat these four product rows
independently. There is no condition that the result be connected to the
old eight-role solution or preserve any old value annotation.

The ten-variable ordering used below is

    ((0,0),(0,1),(0,2),(1,1),(1,2),
     (2,1),(2,3),(3,0),(3,2),(3,3)).                         (2)

This changes the actual coalition law, not merely the certificate for the
old law. In particular prescribed triple 012 or 023 can now occur.

## 2. Complete original-table equations

Set q_(l,i)=0 outside A_l. For S⊆A_l define the literal row probability

    p_l(S)=∏_(i∈S) q_(l,i) ∏_(i∈A_l\S) (1−q_(l,i)).

Write c_l=p_l(∅), C=∏_(l=0)^3 c_l, and

    R_(l,i)=Σ_(∅≠S⊆A_l) p_l(S) r_i(S).

For every interior q, C<1 and the ACTUAL prescribed periodic value is

    V_(l,i) = [Σ_(k=0)^3 (∏_(h=0)^(k−1) c_(l+h)) R_(l+k,i)]/(1−C),   (3)

with phase indices modulo 4 and empty product 1. Equation (3) is the
geometric sum of actual absorption rewards. It is not an unknown tail
payoff chosen separately from the law.

For each of the sixteen pairs (l,i), let O=A_l\{i}. For S⊆O put

    p_l^(−i)(S)=∏_(j∈S)q_(l,j)∏_(j∈O\S)(1−q_(l,j)),
    c_(l,−i)=p_l^(−i)(∅),
    Q_(l,i)=Σ_(S⊆O) p_l^(−i)(S) r_i(S∪{i}),
    H_(l,i)=Σ_(∅≠S⊆O) p_l^(−i)(S) r_i(S),
    D_(l,i)=Q_(l,i)−H_(l,i)−c_(l,−i)V_(l+1,i).             (4)

The ten active ties and six remaining quiet tests are exactly

    D_(l,i)=0 if i∈A_l;       D_(l,i)≤0 if i∉A_l.           (5)

These finite sums include every original coalition reached under the
prescribed law or a current unilateral insertion. For example, the quiet
Quit endpoint of owner 3 at phase 0 includes

    −q_(0,0)q_(0,1)q_(0,2),

from the grand coalition. Owner 1's phase-3 endpoint similarly includes
−q_(3,0)q_(3,2)q_(3,3). Neither term can be inferred from prescribed
support alone; both are explicitly present in (4).

For any legal solution of (5), the deleted cycle survival for owner i is

    C_(−i)=∏_(l=0)^3 ∏_(j∈A_l\{i})(1−q_(l,j))<1.         (6)

The actual value recursion is
V_(l,i)=q_(l,i)Q_(l,i)+(1−q_(l,i))
[H_(l,i)+c_(l,−i)V_(l+1,i)]. Equations (5) bound either current action
by V. Iteration over K cycles leaves at most a bounded remainder times
C_(−i)^K. This tends to zero, including for the complete Never response.
Thus (3)–(6) retain all unrestricted behavioral deviations. This paragraph
only explains the exact test; it does not supply a solution of (5).

## 3. An exact consequence of the newly released role

At an interior solution, owner 1 mixes at phase 1 against owner 2.
Its own singleton and its pair-12 receipt are both 1, so

    V_(1,1)=1.

Put x=q_(0,0), y=q_(0,2), t=q_(0,1). At the newly active phase 0,
owner 1 has exact endpoints

    Q_(0,1)=(1−x)(1−y)+2x(1−y)+(1−x)y
           =1+x−2xy,
    H_(0,1)+c_(0,−1)V_(1,1)
           =4x(1−y)+xy+(1−x)(1−y)
           =1+3x−y−2xy.

Consequently its tie imposes

    y=2x,       in particular 0<x<1/2.                  (7)

The newly selected t does not occur in this equality. This is an exact
original-table restriction on every interior ten-role solution, not a
consequence of the numerical candidate or a generic insertion principle.

## 4. Bounded numerical diagnostic and its limitation

Direct finite-sum evaluation of (3),(4), followed by a ten-variable
`mpmath.findroot` solve of the active part of (5), was used only as a
discovery test. All six quiet tests were evaluated separately, not included
as equalities. The first three runs used 35 decimal digits, tolerance
10^−25 and at most 40 iterations, with seed

    (.0984520158,t,.2206967175,.1820055015,.1882974049,
      .2091849659,.2319783206,.2645181956,t,.1169338769),

for t=.02,.08,.2. These merely initialize the solver; no rate was held
fixed during it. Two further successful runs started at the entire vector
.4 and at (.1,.3,.2,.4,.2,.3,.1,.4,.3,.2), using 28 digits, tolerance
10^−20 and at most 60 iterations. The all-.7 initialization did not
converge. This finite list is not a global root count.

The five successful runs returned the same approximate algebraic candidate
in ordering (2):

    (.1118332103, −.0061930175, .2236664205,
      .1947363361, .1849358258, .1979992853, .2268972575,
      .2520877074, −.0104997325, .1268952669).            (8)

The new hazards q_(0,1) and q_(3,2) are NEGATIVE. Hence (8) is not an
independent stopping law. The rational formulas extend outside the
probability cube; solving that extension does not produce a strategy.
In particular the algebraic cycle value C≈.186303 and the favorable
remaining quiet signs do not certify anything about actual deviations.
In quiet-pair order ((0,3),(1,0),(1,3),(2,0),(2,2),(3,1)), the numerical
D-values at (8) are

    (−.402071,−.223430,−.175135,−.166517,−.113111,−.264686).

Relation (7) is visible in (8), but its proof did not use (8). No rigorous
existence or uniqueness claim is made even about this algebraic candidate.

The first omitted task is therefore legal root production for the explicit
system (3)–(5), not verification of a proposed continuation payoff.
An unsuccessful finite root search cannot prove that this system has no
solution, nor exclude a different stationary or periodic equilibrium.
This bounded operation is stopped here, with no increase in phase count.
