# Fresh radial packet amplification and chronological restart seams

Author: `CODEX_CEDAR`

Status: `ARTIFICIAL_FORCING_ADAPTER_ABSENT; ROUTE EXHAUSTED AT SOURCE INTERFACE`

Current status: the fresh packet supplies the correct all-clock finite-block
contraction, but Section 7 rules out the proposed collapsed-return repair
quantitatively.  At a positive global minimum with total base debt `D>0`, any
finite block whose joint and every player-deleted survival are at most `1-a`
must, at every collapsed vector `(x,x)`, have some prescribed or positive
Snell residual at least `a*D/(2*|I|)`.  Otherwise the exact periodic profile
would have total terminal debt below the global minimum.  For the fresh packet
`a=kappa*scale`, so the desired `o(scale)` residual cannot occur.

Section 5 remains a correct conditional consumer, and Section 6 gives a small
exact boundary example, but they no longer identify a viable producer.  The
no-go shows why exact semantic periodic closing is the wrong target inside the
positive-minimum contradiction: it immediately lands back in the carrier,
where total debt is bounded below by `D`.

The surviving artificial-tail account was tested in Section 8 and fails at a
strictly earlier interface seam: even exact signed cancellation of prescribed
defects does not control the playerwise generated-secant direct-debt account.
Section 9 records that the actual radial declarations expose no rootwise map
from static face balance or quadratic fixed-law remainder to that one-sided
account.  The route is therefore exhausted at the present source interface,
not mathematically refuted under a hypothetical stronger adapter.

Next concrete question after pivot: can a genuinely non-singleton joint Nash
repair phase replace the sequential outsider correction in the paid-row arm,
as the exact deadlock block does?  The first check is the two-player paid-like
best-response cycle already stored in the paid-row notebook: solve its joint
mixed root exactly, then isolate which additional payoff-return and spectator
conditions are still missing from the actual paid source.

This is a distinct pivot from the stopped atom route in
[`CODEX_CEDAR__VANISHING_ATOM_CHRONOLOGY.md`](CODEX_CEDAR__VANISHING_ATOM_CHRONOLOGY.md).
That route found a scale-free semantic debt transfer but ended at a unique
all-Continue cap trap.  The present route starts instead from an actual
finite-prefix all-clock exposure packet.

## 1. Self-contained producer question

Fix a finite player type `I`, a quitting reward table, a positive-minimum
tangent family `frontier`, and

`hcirculation : HasQuittingStoppingLawFlatChargedCirculation
  frontier.positiveDebtSupport frontier.tangent`.

The checked fresh-packet theorem chooses once and for all

- bounded nonnegative radial weights `w`;
- distinct active players `a,b` with `w_a,w_b>0`; and
- `kappa>0`;

such that for every sufficiently large rank `n` there is a finite cutoff
`L_n` for the literal simultaneous packet profile `P_n` satisfying

`kappa*lambda_n <= 1-J_n`,                          (1.1)

`kappa*lambda_n <= 1-S_(n,i)` for every player `i`, (1.2)

where `lambda_n=frontier.scale n`, `J_n` is joint survival through the first
`L_n` live roots of `P_n`, and `S_(n,i)` is survival through the same prefix
with player `i` deleted.  The probability order is literal: first choose rank,
then one common finite cutoff, then (1.1)--(1.2) hold simultaneously for every
deleted player.  There is no limit chosen separately after the player.

Question: from these actual finite blocks, construct for every `eta>0` one
infinite `QuittingChronologicalDebtShadowingCertificate reward eta`.
In particular, one schedule must make both survival products vanish from
every absolute starting time, while the same candidate data have interval-
uniform prescribed discrepancy, suffix-uniform generated-secant adverse
forcing, and all initial candidate debts at most `eta`.

## 2. Named declarations and files inspected

- `QuittingPositiveMinimumDebtTangentFamily.frozenRadialChronologicalData`,
  `frozenRadialChronologicalData_prescribedDefect`, and
  `frozenRadialChronologicalData_directDebtDefect`
  (`SourceMatchedChronologicalData.lean`).
- `frozenRadialRepeatedRoots_opponentSurvival` and
  `frozenRadialRepeatedRoots_jointSurvival`
  (`SourceMatchedRepeatedRootSurvival.lean`).
- `exists_two_positive_frozenRadialCirculationWeights`,
  `exists_frozenRadialFiniteCutoff_joint_and_deleted_exposure`, and
  `exists_frozenRadialBoundedPacketExposure`
  (`RadialPacketExposure.lean`).
- `exists_frozenRadialBoundedResetCube`,
  `frozenRadialFacePayoff_affineRemainderBudget_div_tendsto_zero`, and
  `eventually_all_frozenRadialFacePayoff_affineRemainder_le`
  (`RadialResetCube.lean`).
- `debt_decreasing_reset_does_not_force_opponentExposure` and
  `exact_source_has_zero_forcing_but_unit_initialDebt`
  (`SourceMatchedExposureNoGo.lean`).
- `QuittingChronologicalDebtShadowingCertificate` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`
  (`ChronologicalDebtShadowing.lean`).
- `quittingTerminalSemanticPrefix_within_of_opponentContinueMass_le`
  (`TerminalSemanticPrefixMetric.lean`) and `finiteBlockClosingGap_le` plus
  `finiteBlockClosingGap_le_separateResiduals` (`PeriodicClosing.lean` and
  `PeriodicExceptionalClosing.lean`).

The bounded symbol search covered only these named chronological, fresh-packet,
radial reset-cube, prefix-metric, and periodic-closing files.  It found the
scalar closing consumer used in section 5, but no declaration supplying its
collapsed block residual from the fresh packet.

## 3. Abstract exposure-over-restart amplification

The numerical heart of a possible construction is sound.  Suppose block `n`
has a simultaneous survival loss

`0<a_n<=1`

for joint and every deleted-player clock, and suppose one restart of that
block costs at most `b_n>=0` in a strong additive norm which dominates all
prescribed interval discrepancies and all adverse direct-debt contributions.
Assume

`b_n/a_n -> 0`.                                      (3.1)

For any `eta>0`, choose increasing ranks `n_k` such that

`b_(n_k)/a_(n_k) <= eta*2^(-k-3)`.                   (3.2)

Repeat block `n_k`

`N_k=ceil(1/a_(n_k))`

times in epoch `k`.  Since `a_(n_k)<=1`,

`N_k*b_(n_k) <= (1/a_(n_k)+1)*b_(n_k)`

`                 <= 2*b_(n_k)/a_(n_k)`.             (3.3)

Thus the total additive restart cost over every epoch is at most a convergent
geometric sum, and the constants in (3.2) leave room below `eta`.

For each clock, one block has survival factor at most `1-a_(n_k)`.  Hence the
whole epoch has factor at most

`(1-a_(n_k))^(N_k) <= exp(-N_k*a_(n_k)) <= exp(-1)`.  (3.4)

Every absolute start lies before infinitely many complete future epochs, so
the product of the fixed factors in (3.4) tends to zero.  This proves joint
and every player-deleted tail survival in the correct `for every start`
order.  It also shows why summability of the raw frontier scales is not an
obstruction once a block may be restarted cheaply.

For the actual packet, `a_n=kappa*lambda_n`.  Therefore an additive restart
bound

`b_n=o(lambda_n)`                                    (3.5)

would imply (3.1) and make the amplification available.  This is only an
abstract sufficient lemma.  The strong norm, candidate data, generated
secants, and small initial debt in its premise have not been produced.

## 4. Why the checked `o(lambda)` data is not the restart bound

The radial cube supplies two different small quantities.

First, balance makes the sum of *frozen source edges* in each debt coordinate,
divided by `lambda_n`, tend to zero.  This compares independently reset whole
profiles against one common source.  It is not the full-face path increment
unless the intervening square curvatures are controlled, and even a full-face
semantic comparison would remain static.

Second, every fixed pure-time payoff on the finite radial cube has an affine
remainder `O(lambda_n^2)`, uniformly over faces and pure times.  After division
by `lambda_n` this tends to zero.  This controls cubical nonadditivity when the
same whole-profile witness is transported across reset coordinates.  It does
not compare the shifted tail after `L_n` executed roots with the head at which
the same stopping laws are restarted.

The chronological seam is instead

`tail(P_n,L_n)  ->  head(P_n,0)`                     (4.1)

or a transition from that tail to the head of a later-rank packet.  General
behavior strategies are nonstationary stopping laws.  Conditional survival
through `L_n` ages every law; restarting at time zero resets those ages.  The
frontier fields impose convergence of terminal semantic pairs and normalized
whole-strategy chords, but no shift-covariance, period, or recurrence of the
source strategies.  In particular, at outer radial weight zero `P_n` is just
the source profile, so an `O(lambda_n)` estimate for (4.1) would assert a
head/shift return property of the source which is not present in the
interface.

Reading the chosen roots as one infinite executable schedule does restore
state matching.  `exactOfRoots` then sets every prescribed and direct-debt
defect to zero.  But its time-zero candidate debt is the literal terminal
exploitability of that schedule.  The checked regression demonstrates the
logical separation exactly: zero forcing can coexist with unit initial debt.
Under the assumed positive terminal gap, exact scheduling alone cannot make
all initial debt coordinates arbitrarily small.

## 5. One-block periodic amplification

There is a more economical way to use an `o(scale)` return.  Let

`B=(r_0,...,r_(L-1))`

be any nonempty finite block of product roots.  Write `Phi_B` for composition
of `quittingTerminalSemanticPrefix` through the block, from its boundary tail
back to its head.  For player `i`, let

`J_B=product_(t<L) C_t`

be joint Continue survival, and

`S_(B,i)=product_(t<L) S_(t,i)`

be survival with player `i` deleted.  The prescribed coordinate of `Phi_B`
is an affine scalar map

`z |-> A_(B,i)+J_B*z`.                            (5.1)

The cap coordinate is a scalar Snell map `T_(B,i)`.  Repeated use of the
generated one-step secant, or equivalently of the mass-sensitive prefix
metric, gives

`|T_(B,i)(z)-T_(B,i)(z')| <= S_(B,i)*|z-z'|`.      (5.2)

Suppose one number `a in (0,1]` satisfies

`J_B <= 1-a` and `S_(B,i) <= 1-a` for every `i`.  (5.3)

Let `x` be any payoff vector and use the collapsed semantic reference

`X=(x,x)`.

Assume, for every player,

`|A_(B,i)+J_B*x_i-x_i| <= b`,                     (5.4)

`T_(B,i)(x_i) <= x_i+b`.                          (5.5)

Repeat `B` periodically and let `(V_i,H_i)` be the literal terminal payoff and
behavioral best-response cap at the phase-zero tail.  Periodicity and semantic
prefixing give the exact fixed-point equations

`V_i=A_(B,i)+J_B*V_i`, `T_(B,i)(H_i)=H_i`.         (5.6)

Apply `finiteBlockClosingGap_le_separateResiduals` with common bound
`delta=1-a`, prescribed error `b`, Snell error `b`, and reference `x_i`.
Then

`H_i-V_i <= 2*b/a`.                               (5.7)

This is precisely the terminal semantic debt of the repeated block.  The
argument is against the full behavioral cap: `T_(B,i)` is the one-block Snell
operator, not a stationary or one-shot verifier.

Now use `QuittingChronologicalDebtData.exactOfRoots` on that periodic root
sequence.  Its prescribed and direct-debt forcing vanish exactly, its zero
secants are generated, and its initial candidate debt is the left side of
(5.7).  Condition (5.3) makes joint and every player-deleted survival vanish
from every phase and every absolute start.  Therefore, if

`2*b/a <= eta`,                                    (5.8)

this one exact periodic schedule supplies a complete
`QuittingChronologicalDebtShadowingCertificate reward eta`.

For the actual fresh packet, take the exposing prefix as `B`, with

`a=kappa*frontier.scale(rank)`.

The sole additional quantitative datum needed by this consumer is a vector
`x_rank` for which (5.4)--(5.5) hold with

`b_rank/frontier.scale(rank) -> 0`,                (5.9)

at the **same cutoffs** as the exposure theorem.  Given `eta`, choose a rank
with `b_rank <= eta*kappa*scale(rank)/2`; (5.7) closes the certificate.  This
single-block construction subsumes the numerical epoch calculation in
section 3 and automatically pays every chronological seam through the exact
periodic fixed point.

The natural collapsed vector is `x=frontier.base.1`.  The checked
`allContinue_plateau` implies that the literal all-Continue root fixes the
collapsed pair `(x,x)` as well: every solo reward is at most `x_i`.  But the
fresh block is a prefix of the generally nonstationary source-plus-reset
packet, not a block of all-Continue roots.  The family stores convergence of
the complete terminal semantic pairs of its source profiles, not convergence
of their finite-prefix Bellman action on `(x,x)`.  Hence (5.9) is a new
source adapter, not a consequence of `source_tendsto`.

## 6. Exact rare-root boundary falsifier

The little-o ratio in (5.9) is necessary, even when the roots themselves tend
to all-Continue and the collapsed target is an exact all-Continue Nash target.

Take two players.  A player receives `1` exactly when it Continues and the
other player Quits alone; every quitter and every joint exit receives `0`.
Use the one-root block in which both players Quit with probability
`p in (0,1)`, and repeat it.  For either player, at collapsed scalar tail `x`,

`P_p(x)=p(1-p)+(1-p)^2*x`,                         (6.1)

`T_p(x)=max(0,p+(1-p)*x)`.                         (6.2)

The deleted-player contraction loss is exactly `a=p`; the joint loss is
`2p-p^2>=p`.  The all-Continue root fixes `(0,0)`, and both residuals at zero
tend to zero:

`P_p(0)=p(1-p)`, `T_p(0)=p`.

Nevertheless, for **every** real collapsed target `x`,

`max(|P_p(x)-x|, max(T_p(x)-x,0)) >= p/(3-p)`.      (6.3)

Here is the exact minimization.  If the Continue branch in (6.2) is active
and `x<=1`, divide by `p` and compare

`|(1-p)-(2-p)x|` and `1-x`.

Below `(1-p)/(2-p)`, the second term is at least `1/(2-p)`.  Above that point,
the increasing and decreasing terms meet at

`x=(2-p)/(3-p)`,

where both equal `1/(3-p)`.  If `x>1`, the first term is at least `1`; if the
zero branch of (6.2) is active, the positive cap residual is still larger.
This proves (6.3).

The repeated block can also be solved exactly.  Its prescribed fixed point is

`V=(1-p)/(2-p)`,

its Snell fixed point is `H=1`, and its terminal debt is

`H-V=1/(2-p) -> 1/2`.                              (6.4)

Thus finite exposure plus residuals which merely vanish pointwise do not
produce small periodic debt.  The residual must vanish relative to the
contraction loss.  This two-player table is a boundary regression for the
consumer, not a counterexample to the actual charged-circulation packet: it
does not realize the frontier's frozen balance datum.

## 7. Quantitative no-go at a positive global minimum

The proposed collapsed block return is not merely absent from the source
interface.  It is incompatible with the positive-minimum hypothesis at the
scale needed in Section 5.

Let

`D=quittingTerminalSemanticDebtSum frontier.base>0`

and let `N=|I|`.  Take any nonempty finite root block `B` for which joint and
every player-deleted survival are at most `1-a`, with `0<a<=1`.  Repeat `B`
periodically, and write `(V_i,H_i)` for the literal phase-zero terminal
prescribed payoff and unrestricted behavioral cap.  This is an actual
behavioral profile, so `frontier.base_minimum` gives

`D <= sum_i (H_i-V_i)`.                             (7.1)

Fix an arbitrary collapsed reference vector `x`.  For each player put

```text
e^P_i = |A_(B,i)+J_B x_i-x_i|,
e^T_i = max(T_(B,i)(x_i)-x_i,0).
```

Both are nonnegative.  The definition of `e^T_i` gives
`T_(B,i)(x_i)<=x_i+e^T_i`.  Apply the checked theorem
`finiteBlockClosingGap_le_separateResiduals` with
`delta=1-a`, `etaV=e^P_i`, and `etaB=e^T_i`.  The exact periodic fixed-point
equations and the two survival bounds give

`H_i-V_i <= (e^P_i+e^T_i)/a`.                      (7.2)

Summing (7.2) and using (7.1) yields the exact necessary residual budget

`a*D <= sum_i (e^P_i+e^T_i)`.                      (7.3)

Consequently

`max_i max(e^P_i,e^T_i) >= a*D/(2*N)`.             (7.4)

The player type is nonempty here because `D>0`.  No compactness, limiting
profile, or selected target is used in (7.4); it holds for every finite block
and every collapsed vector.

For an exposing fresh radial packet, one may take
`a=kappa*frontier.scale(rank)`.  Therefore every exposing cutoff and every
choice of `x_rank` satisfy

```text
max_i max(e^P_(rank,i),e^T_(rank,i)) /
  frontier.scale(rank) >= kappa*D/(2*N)>0.          (7.5)
```

This exactly negates (5.9).  The rare-root bound in Section 6 is a concrete
sharper instance of the same phenomenon, but (7.4) applies to the actual
positive-minimum frontier without constructing a special table.

The obstruction is also conceptually sharp.  `exactOfRoots` uses literal
semantic tails, and periodic closing selects literal semantic fixed points;
both land in the terminal semantic carrier and hence inherit the positive
minimum.  Chronological debt shadowing can contradict that minimum only by
using non-tautological candidate values and debts whose discrepancy is spread
through the allowed forcing budgets.  A future radial construction must pay
the lower bound (7.3) globally rather than assume it disappears locally.

## 8. Signed target forcing does not pay deleted-clock forcing

The smallest exact packet already separates the two accounts in the
chronological certificate.  Return to the two-player one-root table of
Section 6 and write

```text
s=1-p,
P(u)=p*s+s^2*u,
T(h)=p+s*h,
V=s/(1+s)=s/(2-p).
```

The displayed branch of `T` is active at all nonnegative candidate caps.
Repeat the same product root, but let the artificial prescribed candidates
alternate

`u_0=V+c`, `u_1=V-c`,

where `|c|<=V/2`.  Put `j=s^2`.  Since `V=P(V)`, the two one-step prescribed
defects are exactly

```text
f^P_0 = u_0-P(u_1) = (1+j)c,
f^P_1 = u_1-P(u_0) = -(1+j)c.                     (8.1)
```

Thus every unweighted interval sum of prescribed defects has absolute value
at most `(1+j)|c|`.  The target-forcing field can be made arbitrarily small,
and its full two-step sum vanishes exactly.

Now allow arbitrary nonnegative two-periodic candidate debts `d_0,d_1`.  The
semantic debt generated at phase `t` from successor candidate
`(u_(t+1),u_(t+1)+d_(t+1))` is

```text
q(u_(t+1))+s*d_(t+1),
q(u)=T(u)-P(u)=p*(p+s*u).
```

Hence the direct debt defects are

```text
g_0=d_0-q(u_1)-s*d_1,
g_1=d_1-q(u_0)-s*d_0.                              (8.2)
```

The actual repeated tail has cap `H=1`.  Both the candidate and actual caps
remain on the same affine branch, so the generated secant is exactly `s`,
which is also the deleted-player Continue mass.  The infinite adverse direct
forcing from the two phases is therefore

```text
A_0 = [q(u_1)+s*q(u_0)]/(1-s^2)-d_0
    = 1/(2-p)-p*(1-p)*c/(2-p)-d_0,

A_1 = [q(u_0)+s*q(u_1)]/(1-s^2)-d_1
    = 1/(2-p)+p*(1-p)*c/(2-p)-d_1.                (8.3)
```

All dependence on the *later* debt bank cancels.  This is the exact weighted
coboundary: favorable direct defect created by raising the later candidate
debt merely repays the earlier cost after the same deleted-clock discount.
Only the debt already stored at the suffix's starting phase subtracts from
its adverse account.

In particular, with `d_0=d_1=0`,

`max(A_0,A_1)>=1/(2-p)`.                           (8.4)

The lower bound tends to `1/2` although the root's quitting probability and
each one-step defect tend to zero.  Taking `c=0` makes the prescribed defects
identically zero while leaving `A_0=A_1=1/(2-p)`.  More generally, imposing
initial debt `d_0<=eta` and prescribed discrepancy
`(1+s^2)|c|<=eta` leaves

```text
A_0 >= 1/(2-p)-p*s*eta/((1+s^2)*(2-p))-eta,
```

which stays uniformly positive for small `eta`.

This packet is still a boundary regression rather than an actual charged
radial frontier.  Its role is exact: signed prescribed/target balance and
deleted-clock direct forcing are different certificate fields.  A static
radial identity which cancels terminal payoff or debt chords does not control
the playerwise one-sided quantity in (8.3).  An actual adapter must provide a
rootwise Nash/debt mechanism or an equally explicit future favorable direct
defect for every suffix; label balance alone cannot be read as that account.

## 9. Exact actual-source adapter deficit

The named radial data live at three different levels.

1. Frozen balance compares terminal semantic-debt coordinates of complete
   reset-cube **head profiles** at one common source rank.
2. The quadratic affine remainder compares terminal payoff of one fixed
   pure-time law across reset faces, again for complete head profiles.
3. Packet exposure supplies one finite cutoff with lower bounds on joint and
   every player-deleted absorption loss.

The chronological certificate asks for different objects.  At an executed
root `r_t` and artificial successor `(u_(t+1),u_(t+1)+d_(t+1))`, it needs the
one-step quantities

```text
u_t - Prefix(r_t,(u_(t+1),u_(t+1)+d_(t+1))).prescribed,

d_t - debt(Prefix(r_t,(u_(t+1),u_(t+1)+d_(t+1)))),
```

plus the secant generated by comparison with the literal reached tail.  None
is a terminal reset-cube edge.  Consecutive candidate heads need not be the
shifted tail of the profile from which `r_t` was sampled.

The declaration
`frozenRadialChronologicalData` avoids this mismatch only by using literal
reached-tail semantics.  Then both defects vanish, but the initial candidate
debt is the actual positive-minimum carrier debt.  The packet exposure theorem
avoids label switching by taking roots from one simultaneous packet profile,
but supplies no artificial successor pairs.  The pure-time affine-remainder
theorems have no time-shift, Bellman-prefix, candidate-debt, or generated-
secant conclusion.

Section 8 shows that this is not a cosmetic missing rewrite.  Perfectly
balanced prescribed defects can coexist with an order-one adverse direct
account after deleted-clock amplification.  The direct account is playerwise
and one-sided; tangent circulation across movers or total debt coordinates
cannot be substituted for it without a new theorem preserving the time and
conditioning order.

Therefore an actual continuation of this route must add a new source theorem
which directly constructs bounded artificial `u_t,d_t` and proves both:

- interval-uniform unweighted prescribed-defect bounds; and
- suffix-uniform generated-secant-weighted adverse direct-debt bounds,

while retaining the already checked packet exposure.  An equivalent stronger
datum would be a rootwise approximate-Nash/Bellman continuation assignment
whose local debts are already summable after deleted-clock weighting.  No
named declaration inspected here supplies either datum.

This is the precise adapter deficit.  The abstract packet regression does not
prove that the full charged-circulation hypotheses cannot imply such a new
theorem; it proves that static signed balance and exposure alone are not the
required account.  I stop this route rather than recycle the label cycle or
the now-impossible collapsed periodic return.

## Proved or checked here

- Equations (1.1)--(1.2) are the exact quantifiers of the named checked fresh
  packet theorem.
- The amplification calculation (3.1)--(3.4) is proved in ordinary
  mathematics.  It treats joint and every deleted-player clock simultaneously
  and is uniform over every suffix start.
- The one-block closing implication (5.3)--(5.8) follows from the checked
  scalar fixed-point theorem `finiteBlockClosingGap_le_separateResiduals` and
  the exact periodic/exact-data semantics.  Its conclusion covers unrestricted
  behavioral deviations.
- The rare-root lower bound (6.3) and exact periodic debt (6.4) are proved by
  exact algebra.
- The positive-minimum lower bound (7.3)--(7.5) follows from
  `frontier.base_minimum`, the actual periodic profile, and the checked
  separate-residual closing theorem.  It rules out the formerly requested
  `o(scale)` collapsed return for the actual exposing packet.
- The two-phase calculation (8.1)--(8.4) is exact.  It gives zero signed
  prescribed forcing but a positive deleted-clock adverse-direct account and
  shows precisely how candidate-debt buffers telescope.
- The distinction between frozen cube edges, pure-time affine remainder, and
  the chronological restart seam is a declaration-level interface audit.

No new Lean result or full certificate is claimed.

## Open claims and objections

- A state-matched restart could exist for a more carefully selected cutoff,
  but it cannot have the uniformly `o(scale)` collapsed residuals in (5.9).
- A noncollapsed two-coordinate semantic return is not ruled out by (7.4),
  but using its literal positive debt cannot make the chronological
  certificate's initial debt small.
- One might rebase the next packet at the actual shifted tail instead of
  restarting its head.  No tangent or charged-circulation adapter is available
  at that new source.
- Even a proved seam cost `o(lambda)` must be expressed in the exact
  prescribed/direct/generated-secant certificate fields, not only as semantic
  pair distance or total-debt displacement.
- The amplification does not solve initial small debt.  That field needs a
  separate artificial-candidate or return construction compatible with the
  same repeated blocks.

## Requested check

For any future radial adapter, exhibit the explicit formulas for artificial
candidate tails and check the two forcing fields above in their literal
probability order.  Without such new data, continue instead with the paid-row
joint-phase repair question described near the top.
