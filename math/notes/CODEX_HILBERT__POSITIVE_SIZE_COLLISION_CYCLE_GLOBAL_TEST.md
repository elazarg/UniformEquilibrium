# Positive-size collision roots: a global cycle test that collapses to a pure consumer

Owner: CODEX_HILBERT. Ordinary exact calculation, not independently reviewed
or Lean-checked. This bounded test genuinely uses collision rewards and a
closed positive-charge path. It excludes every polynomial certificate on
the displayed table, but the table also has a pure equilibrium. Therefore
it supplies no new unsolved table class. The completion is not to be tuned
to hide that simpler consumer.

## 1. Precise question and raw two-root test

For a canonical four-player table r with singleton vector (1,0,0,0), let
all players use independent stopping laws and let Never pay zero. Consider
the two positive-size product roots

    qᴬ=(1/2,1/2,0,0),       qᴮ=(0,0,1/2,1/2).

Each has absorption 3/4. Write r_j=r({j}) and define from the raw table

    A=r_0+r_1+r({0,1}),     B=r_2+r_3+r({2,3}),
    vᴬ=(4A+B)/15,          vᴮ=(A+4B)/15.                (1)

These are the unique solutions to vᴬ=(A+vᴮ)/4 and
vᴮ=(B+vᴬ)/4. Thus Bellman matching for this chosen period is automatic
from (1); its root Nash conditions must still be checked.

They are four active-player linear equalities

    vᴬ_i=(s_i+r_i({0,1}))/2  for i=0,1,
    vᴮ_i=(s_i+r_i({2,3}))/2  for i=2,3,

and four passive inequalities

    [s_i+r_i({0,i})+r_i({1,i})+r_i({0,1,i})]/4 ≤ vᴬ_i
                                              for i=2,3,
    [s_i+r_i({2,i})+r_i({3,i})+r_i({2,3,i})]/4 ≤ vᴮ_i
                                              for i=0,1.       (2)

The active equalities, together with mixed Bellman matching, imply equality
of Quit and Continue. A passive player prescribes Continue, so its displayed
value already equals that endpoint; (2) checks the other action.

If these finite raw tests hold, the forward annotation relation contains

    vᴮ —qᴬ→ vᴬ —qᴮ→ vᴮ.                               (3)

Both rows have zero regret and zero Bellman error. The actual values lie
in the reward box because the repeated profile absorbs almost surely.
Consequently (3) lies in every positive-tolerance floor-free relation in
the padded reward box. Any proposed all-edge potential, polynomial or not,
would give 0≥3/2 after summation.

This is a finite raw test for one selected root pattern, not a theorem that
arbitrary tables satisfy it or that the fixed half-hazards are complete.
The research question was whether an exact instance could avoid both the
known homogeneous singleton branch and an already available stationary
consumer. The latter test fails below.

## 2. Complete canonical table tested

| S | r(S) |
| --- | --- |
| {0} | (1,3,−1,−1) |
| {1} | (4,0,−1,−1) |
| {2} | (0,−1,0,3) |
| {3} | (0,−1,3,0) |
| {0,1} | (3,2,−3,−3) |
| {0,2} | (1,−4,0,−4) |
| {0,3} | (1,−4,−4,0) |
| {1,2} | (−4,0,0,−4) |
| {1,3} | (−4,0,−4,0) |
| {2,3} | (−2,−3,2,2) |
| {0,1,2} | (−4,−3,−5,−4) |
| {0,1,3} | (−4,−3,−4,−5) |
| {0,2,3} | (−4,−4,−4,−3) |
| {1,2,3} | (−4,−5,−4,−3) |
| {0,1,2,3} | (−5,−5,−5,−5) |

Here M=5 is a reward bound. Formula (1) gives

    vᴬ=(2,1,−1,−1),       vᴮ=(0,−1,1,1).

Exact evaluation of the endpoints gives

| Root and continuation | Quit endpoints | Continue endpoints | Prescribed value |
| --- | --- | --- | --- |
| qᴬ against vᴮ | (2,1,−5/4,−5/4) | (2,1,−1,−1) | vᴬ |
| qᴮ against vᴬ | (−1/4,−5/4,1,1) | (0,−1,1,1) | vᴮ |

Thus (2) and (3) hold exactly, with strictly optimal Continue for every
passive player. The active coordinates are genuinely mixed. This is not
a single-owner or infinitesimal-root calculation.

## 3. Every behavioral response is controlled

Chronological play alternates qᴬ then qᴮ. Joint survival per period is
1/16. For every player, the opponents' survival per period is 1/8: one
partner contributes 1/2 in its own phase and the other pair contributes
1/4 in the other phase. Hence all prescribed and deleted survival tails
vanish geometrically.

The exact endpoint maxima in the table equal the prescribed phase values.
Backward induction bounds any deviation that stops by a finite date or then
uses a bounded terminal continuation. The remaining continuation error is
at most a constant times the opponent-deleted survival, which tends to
zero. Thus every finite pure stopping date and Never has payoff at most
the displayed phase value. Taking averages covers all independent complete
behavioral replacements. The alternating profile is exact terminal Nash.

This verifies the actual periodic semantics of (3); it is stronger than
merely solving free annotation equations. The standard terminal consumer
gives a uniform-equilibrium payoff. No floor was used in obtaining the
polynomial contradiction, and semantic punishment normality is automatic
from the canonical singleton vector.

## 4. Decisive simpler equilibrium and sure-root guard

Let players 1 and 3 Quit surely at date zero, with 0 and 2 choosing Never.
The payoff is r({1,3})=(−4,0,−4,0).

- If owner 1 delays or chooses Never, player 3 still quits at zero, giving
  owner 1 the value r_1({3})=−1<0. Likewise owner 3 would get
  r_3({1})=−1<0.
- Outsider 0 can only change the outcome by joining at zero, which gives
  r_0({0,1,3})=−4, exactly its current value.
- Outsider 2's joining payoff is r_2({1,2,3})=−4, also unchanged.

Every later date is already preempted, and averaging cannot improve these
pure comparisons. This is an exact terminal equilibrium at date zero,
and directly a uniform equilibrium at every horizon.

In addition the sure-root condition C_sure holds without computing P.
At q=(0,1,0,1), deleting any one player still leaves a sure quitter.
Therefore every root comparison is independent of its continuation vector,
and the preceding endpoint checks apply in particular against P. The
semantic guard for a negative certificate is thus not excluded here.

This pure equilibrium is the stopping reason for the candidate, not a
numerical search failure. An exploratory numerical search for an interior
stationary root supplied no proof and is not used in any conclusion.

## 5. Matrix and source comparison

The singleton comparison matrix is

    Γ = [ 0  3 −1 −1 ]
        [ 3  0 −1 −1 ]
        [−1 −1  0  3 ]
        [−1 −1  3  0 ],

with positive inverse (1/15) times

    [2 7 3 3; 7 2 3 3; 3 3 2 7; 3 3 7 2].

As previously proved for this same matrix, it has full standard Q and no
homogeneous simplex solution, while an opposite 2×2 principal fails
projective Q. The matrix calculation alone therefore does not identify
the simple equilibrium above. The different completion in
`CODEX_RENY__COLLISION_TWO_PHASE_INVERSE_DESIGN_TEST.md` already exhibited
the same danger: its collision cycle also had an old stationary consumer.
That note additionally proves that this Γ admits no balanced singleton
cycle of any length. None of these matrix properties implies that a new
collision completion is outside the existing strategic classes.

The exact periodic source correspondence was checked in
`UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`, notably
`sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile`,
`IsQuittingCyclicResponseSolution`, and
`quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution`.
These already provide the unrestricted cap compiler; the finite table
test is not a new semantic consumer.

**Outcome:** (3) is an exact all-edge cycle, not a degree restriction or a
local principal screen, but the attempted new-coverage claim fails. No
collision entries are adjusted further. The next meaningful question is a
raw-table condition that produces such a cycle without first prescribing
its rewards, with separate exclusion of already solved stationary/sure-root
cases, or an exhaustive obstruction to that condition. This note supplies
neither such general condition nor a new hard-residual producer.
