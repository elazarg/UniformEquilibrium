# CODEX_CEDAR — conditioned atom-clock reprojection

## Current best attempt

**Exact reviewable claim.**  A countable chain of finite literal root blocks
carrying bounded nonnegative candidate semantic pairs can be concatenated
without re-solving every row.  If the terminal candidate pair at the donated
end of block `k` and the initial candidate pair of block `k+1` have
coordinatewise seam mismatches `A_{k,i}` in prescribed payoff and `B_{k,i}`
in the all-behavior cap, then the inherited candidate
data have prescribed defect at that seam at most `A_{k,i}` and direct-debt
defect at most `A_{k,i}+B_{k,i}`.  All nonseam defects are zero.  Summable
seam mismatches, small initial candidate debt, and two persistent literal
clock labels therefore give a full
`QuittingChronologicalDebtShadowingCertificate`.  This is Propositions 1--2.
Conversely, vanishing literal clocks make such bounded annotations rigid:
their initial prescribed payoff and cap differ from the actual infinite
concatenated profile by at most the total prescribed and cap seam prices.
Thus a positive global minimum `Delta` of terminal debt forces the total seam
toll plus artificial initial debt to be at least `Delta`.  This is Proposition
3 and Corollary 3A.
The toll need not be adverse: at a seam, a donated successor cap above the
next block's cap produces a nonnegative direct-debt defect, up to the
prescribed-payoff mismatch.  Consequently cap drops may be arbitrarily large
or nonsummable while every-suffix adverse forcing is controlled solely by the
summable prescribed seam.  This exact one-sided adapter is Proposition 4 and
Corollary 4A.
For the actual positive-minimum replacement, however, the mover's own cap is
unchanged because only that mover's strategy is replaced.  Its debt reduction
is exactly its prescribed-payoff increase, so the favorable direct defect is
paired one-for-one with an opposite prescribed defect.  Proposition 5 shows
that a cross-player cap pump or a genuine Bellman return—not the own
replacement alone—is necessary.
There is one exact way a Bellman return can use the otherwise conservative
toggle: if its prescribed and direct seam defects alternate with a common
amplitude at most `eta`, every interval has prescribed discrepancy at most
`eta`, and every secant-weighted adverse sum is at most `eta` by the
alternating-series bound.  Proposition 6 reduces this route to constructing
an actual small-amplitude Bellman shuttle with clocks.
A second route avoids seam return entirely.  An exact Bellman spine may use
roots that are only approximately Nash, provided player `i`'s one-row Nash
gap is at most `eta` times the probability that an opponent absorbs at that
row.  Because every generated secant is bounded by opponent Continue mass,
the adverse errors telescope to at most `eta` on every suffix.  Proposition 7
reduces clock doping to this scale-free cross-player incentive ratio.
That ratio cannot be met by indiscriminately shrinking rare Quit hazards: if
all players strictly prefer Continue by at least `a`, summing the playerwise
inequalities forces every Quit hazard to vanish whenever
`eta<a/(|I|-1)`.  Proposition 8 isolates the necessary near-indifference or
sure-Quit source datum.

**Status and main gap.**  Propositions 1--7 are proved below as ordinary
mathematics and independently reviewed; Proposition 7's normalized-incentive
compiler has two independent reviews.  Proposition 8 is a proved elementary
obstruction awaiting independent review.  The earlier absolute-seam route is
closed by semantic rigidity; signed cap drops and balanced shuttles survive
analytically but lack an actual reached-tail Bellman return.  The sharpest
remaining gap is now upstream and single: no construction supplies one
bounded exact Bellman spine whose literal roots have two persistent labels
and whose playerwise diagonal root Nash gaps satisfy the normalized incentive
bound at every requested accuracy.

**Conjecture-closing thesis.**  Start from the bounded Nash--Bellman
predecessor relation and select, for every `eta>0`, one exact Bellman spine
`(v_t,q_t)` such that

\[
 g_{t,i}\le\eta(1-O_{t,i})                               \tag{0.1}
\]

for every player and date, while two fixed marginal Quit streams diverge.
Proposition 7 then supplies the full chronological certificate with diagonal
candidate debt zero.  Atom/reset data are useful only if they force the
cross-player near-indifference needed for (0.1) against this same Bellman
continuation; raw incidence alone is insufficient.

**Universal obligation changed.**  It is no longer necessary to transport
absolute cap seams or an actual low-debt semantic source.  The exact required
object is a bounded sequence satisfying exact prescribed Bellman evaluation,
the two literal clock fields, and (0.1).  Proposition 8 shows this condition
is scale-free: on a root where every player has Continue advantage at least
`a`, it permits no positive hazard once `eta<a/(|I|-1)`.  Thus a successful
producer must expose near-indifference or a Quit-favoring action on every
clock-carrying layer, with the opponent hazard paying each player's own
mixing loss.

**Kill criterion.**  Abandon this route if the actual positive-minimum data
admit a uniform constant `c>0` such that every bounded exact-Bellman,
two-clock root sequence has some date/player with

\[
 g_{t,i}>c(1-O_{t,i}),
\]

and the failure of that ratio does not itself trigger a known exact endpoint.
Merely finding an all-Continue exact Nash--Bellman spine is not progress: it
has zero gap but no clock.  Merely adding rare hazards is not progress either,
because Proposition 8 shows that strict action gaps survive the scaling.

**Sections to check.**  Section 2 lists the exact source declarations;
Section 3 proves the one-seam inequalities; Section 4 gives the summable-seam
certificate; Sections 5--6 isolate the actual-source deficit and boundary
falsifiers; Section 8 proves semantic rigidity and the quantitative seam
toll; Section 9 proves the signed cap-drop adapter; Section 10 proves the
own-replacement conservation law; Section 11 proves the alternating-shuttle
forcing lemma; Section 12 proves the normalized incentive compiler; Section
13 proves the strict-Continue obstruction to rare-hazard doping; Section 14
records the proved/open boundary and exact next check.

## 1. Self-contained question

Let `I` be finite.  Fix a reward table `r` with

\[
 |r(S)_i|\le M
\]

for every nonempty terminal coalition and player.  For each `k`, let
`N_k>=1`, let `q_{k,t}` be literal product roots for `0<=t<N_k`, and attach
candidate semantic pairs

\[
 X_{k,t}=(u_{k,t},b_{k,t})
\]

for `0<=t<=N_k`.  These pairs need not be complete terminal semantic pairs of
behavioral profiles.  Their candidate debts `b_{k,t}-u_{k,t}` will be required
nonnegative, and inside each block they obey the exact Bellman recursion

\[
 X_{k,t}=\operatorname{Prefix}_{q_{k,t}}(X_{k,t+1}).       \tag{1.1}
\]

Concatenate the literal roots in chronological order.  At a seam, the
candidate successor changes from `X_{k,N_k}` to the next block source
`X_{k+1,0}`.  Define

\[
 A_{k,i}=|u_{k,N_k,i}-u_{k+1,0,i}|,
 \qquad
 B_{k,i}=|b_{k,N_k,i}-b_{k+1,0,i}|.                       \tag{1.2}
\]

The question is whether actual atom/reset data can provide these candidate
annotations so that the seam prices are summable, the first artificial
candidate debt is arbitrarily small, and the literal root chronology retains
two persistent labels.

## 2. Bounded source audit

The board and `questions/CONDITIONED_PACKET_REPROJECTION.md` were refreshed.
A narrow symbol search inspected the following declarations.

- `exists_executable_positiveIncidence_normalizedReprojectionGerm` and
  `exists_sameProfile_finiteWindow_defectPacket`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionWindow.lean`)
  give complete executable profiles, one fixed positive-incidence coalition,
  drifting finite windows, and a universal moving-mark owner-defect estimate.
- `QuittingReprojectionDiffuseWindowPacket.eventually_matchedChronology`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionDiffuseClockBridge.lean`)
  gives exact semantic prefixing on every fixed finite depth of each one
  profile.  It makes no equality or convergence claim between the endpoint of
  one selected profile and the source of the next.
- `resetFace_globalMinimum_or_surfaceTension_reprojectionCostate`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetFaceReprojection.lean`)
  retains the static reset-face costate, but does not select a chronological
  successor on its carrier.
- `quittingRootSuccessorPayoff_sub_eq_continueMass_mul` and
  `abs_quittingRootSuccessorPayoff_sub_le_fixedOpponentsContinueMass_mul`
  (`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`) give the
  prescribed-coordinate one-step sensitivity.
- `exists_quittingTerminalSemanticPrefix_secant` and
  `QuittingChronologicalDebtShadowingCertificate`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`)
  give the generated cap secant and the exact downstream fields.
- `abs_quittingRootSequenceTerminalValue_sub_le_of_prefix_eq` and
  `abs_quittingRootSequenceBestResponseValue_sub_le_of_prefix_eq`
  (`UniformEquilibrium/Quitting/Terminal/TailCompression/ElementaryCaps.lean`)
  are the already checked global common-prefix versions: prescribed changes
  are priced by joint survival and unrestricted behavioral caps by the
  player-deleted survival.
- `semanticPair_eq`, `jointSurvival_eq`, and `deletedSurvival_ne`
  in the explicit regression
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean`
  show that a semantic pair plus joint survival does not determine a labelled
  deleted clock.
- `QuittingChronologicalDebtData.exactOfRoots` and its zero-defect theorems
  (`UniformEquilibrium/Quitting/Debt/Dynamic/ExactChronologicalData.lean`)
  show that literal concatenation itself is executable.  This bookkeeping
  does not make its actual initial terminal exploitability small.

No declaration found in this bounded search states the summable semantic-cap
seam adapter below.

## 3. One exact seam

Fix a product root `q` and two candidate successor semantic pairs

\[
 X=(u,b),\qquad Y=(u',b').
\]

Let `F_q` denote `quittingTerminalSemanticPrefix r q` and fix player `i`.
Put

\[
 J(q)=\Pr_q(\text{everyone Continues}),\qquad
 O_i(q)=\Pr_q(\text{every opponent of }i\text{ Continues}).
\]

### Proposition 1 (seam-price inequalities)

The prescribed and cap coordinates satisfy

\[
 |F_q(X).1_i-F_q(Y).1_i|
   =J(q)|u_i-u'_i|,                                      \tag{3.1}
\]

\[
 |F_q(X).2_i-F_q(Y).2_i|
   \le O_i(q)|b_i-b'_i|.                                 \tag{3.2}
\]

Consequently their debt coordinates `d=b-u` satisfy

\[
 |d(F_q(X))_i-d(F_q(Y))_i|
 \le J(q)|u_i-u'_i|+O_i(q)|b_i-b'_i|.                    \tag{3.3}
\]

In particular, the right sides are bounded by `A_i` and `A_i+B_i`
respectively.

#### Proof

The first prefix coordinate is the root successor payoff.  The absorbing
contribution is independent of the successor, and only the all-Continue
outcome reads `u_i`; this is exactly
`quittingRootSuccessorPayoff_sub_eq_continueMass_mul`.

For the cap coordinate, pure Quit at the displayed row absorbs and is
independent of the successor.  Pure Continue has an absorbing contribution
independent of the successor plus `O_i(q)b_i`.  Thus the cap is

\[
 \max\{Q_i(q),\ C_i(q)+O_i(q)b_i\}.
\]

The map `z -> max(Q,C+O_i z)` is `O_i`-Lipschitz because `O_i>=0`, proving
(3.2).  Finally `d(F_q(X))_i=F_q(X).2_i-F_q(X).1_i`; the triangle inequality
with (3.1)--(3.2) proves (3.3).

The cap calculation is also the formula used in
`exists_quittingTerminalSemanticPrefix_secant`, so it covers a switch of the
maximizing Quit/Continue branch.  No endpoint-Nash or stationary assumption
is present.

## 4. Summable seam concatenation

At a global row belonging to local time `t` of block `k`, set the candidate
prescribed value to `u_{k,t}` and candidate debt to `b_{k,t}-u_{k,t}`.  The
global next candidate at an internal row is `X_{k,t+1}`; at the last row it is
`X_{k+1,0}`.

### Proposition 2 (seam-only conditioned packet adapter)

Assume `eta>0` and the following exact conditions.

1. Every candidate pair satisfies (1.1), its debt is coordinatewise
   nonnegative, and there are finite constants `C,D` such that
   `|u_{k,t,i}|<=C` and `|b_{k,t,i}-u_{k,t,i}|<=D` for every `k,t,i`.
   No candidate pair is assumed to be an actual terminal semantic pair.
2. For every player `i`, the first candidate debt obeys
   `b_{0,0,i}-u_{0,0,i}<=eta`.
3. For every player `i`,

   \[
   \sum_k A_{k,i}\le\eta,
   \qquad
   \sum_k(A_{k,i}+B_{k,i})\le\eta.                        \tag{4.1}
   \]

4. The concatenated literal roots have two distinct persistent marginal
   labels (equivalently, every player-deleted survival vanishes on every
   suffix).

Then there is a
`QuittingChronologicalDebtShadowingCertificate reward eta` on the literal
concatenated roots.

#### Proof

At an internal row the actual template successor is exactly the next global
candidate, so both candidate defects vanish by (1.1).  At a seam, Proposition
1 gives

\[
 |\operatorname{prescribedDefect}_{k,i}|\le A_{k,i},
 \qquad
 |\operatorname{directDebtDefect}_{k,i}|
   \le A_{k,i}+B_{k,i}.                                  \tag{4.2}
\]

Hence any finite interval contains a subset of the seams and its signed
prescribed-defect sum has absolute value at most the first series in (4.1).

For each global row and player, apply
`exists_quittingTerminalSemanticPrefix_secant` to the candidate successor
pair and the literal semantic pair of the actual next global suffix.  Choose
the resulting secant.  It is nonnegative, is at most the player-deleted
Continue mass, and has the required generated identity.  Every product of
such secants lies in `[0,1]`; therefore, for every finite suffix,

\[
 -\sum_t w_{t,i}\operatorname{directDebtDefect}_{t,i}
 \le \sum_k |\operatorname{directDebtDefect}_{k,i}|
 \le\eta.                                                \tag{4.3}
\]

This is stronger than the eventual `eta+slack` adverse-forcing field.

Candidate debts are nonnegative and prescribed values/debts are uniformly
bounded by item 1.  The initial-debt field is item 2.  Item 4 and the exact two-label
characterization give joint and every-player-deleted survival on every
suffix.  These are all fields of the chronological certificate.

### What this changes

The source-changing theorem need not make every row of a donated block close
to a separately frozen semantic row.  An exact bounded *candidate* Bellman
block makes every internal row perfect, even when its first candidate debt is
not the actual debt of the root profile.  Only the two coordinates at
countably many block seams are charged, and only their total `l1` mismatch
matters.

## 5. Exact route versus candidate route

Using `exactOfRoots` on the same concatenated roots sets both defect series to
zero, but replaces the inherited candidate debt by the *actual* terminal
exploitability of the new infinite profile.  Thus its only missing certificate
field is small actual initial debt.  Requiring that for every accuracy is a
direct approximate-terminal-Nash construction, not a conditioned adapter
deduced from the static atom access.  Proposition 2 deliberately permits
nonsemantic candidate pairs so that small candidate debt and a one-sided seam
budget can be proved upstream without first proving any donor or concatenated
profile nearly Nash.

The generic common-prefix bounds from `ElementaryCaps.lean` give the same
warning quantitatively.  Replacing a tail after a prefix changes prescribed
payoff by at most `2M` times joint survival and changes the unrestricted
behavioral cap for `i` by at most `2M` times the deleted survival.  A single
positive clock quota gives only a fixed contraction, not an error tending to
zero.  Repeating independently selected atom blocks creates the clocks but
does not make the first frozen source profile agree with that longer prefix.

## 6. Boundary tests and exact remaining producer

1. **The cap seam is indispensable.**  At an all-Continue root, take two
   successor caps above the corresponding solo reward.  The prefix cap reads
   the successor cap with coefficient one.  A fixed nonzero `B_{k,i}` then
   appears unsuppressed in the direct-debt defect.  Prescribed payoff matching
   alone cannot imply (4.1).
2. **Semantic pair plus joint survival does not carry clocks.**  The checked
   `QuittingCommonWitnessNoncompositionality` profiles have equal complete
   semantic pairs and equal first-stage joint survival but unequal owner-
   deleted survival.  Proposition 2 avoids this falsifier by carrying the
   literal root blocks and their labelled marginal hazards in addition to the
   semantic seam pairs.
3. **Arbitrary-depth matching inside one profile is not seam matching.**
   `eventually_matchedChronology` supplies one semantic special case of (1.1)
   for every fixed depth of a source profile.  It neither supplies a
   nonsemantic small-debt initial candidate nor compares `X_{k,N_k}` with
   `X_{k+1,0}` when `N_k` and the selected profile rank both move.  Compactness
   of the initial semantic/law points does not identify that shifted endpoint.
4. **A frozen atom is insufficient.**  One may repeat a finite root block to
   obtain divergent clocks, but the repeated block's new continuation cap is
   not the donated profile's cap.  Unless that block is an exact semantic
   return, the fixed seam mismatch repeats and violates (4.1).

The next concrete check is therefore:

> Does the actual normalized reprojection construction provide bounded
> nonnegative candidate Bellman blocks with small first debt and cutoffs
> `N_k`, plus a successor selection for which `X_{k,N_k}` approaches
> `X_{k+1,0}` at a preassigned summable rate, while the literal roots retain
> the fixed terminal/mover labels?

The present source gives convergence of initial semantic/law points and
unbounded window lengths, separately.  It gives no shifted-endpoint
precompact recurrence, artificial small-debt candidate chain, or one-sided
seam potential.  That is the exact adapter deficit; no full conjecture or Lean
theorem is claimed here.

## 7. Proved and unproved separation

**Proved here as ordinary mathematics:** Proposition 1's exact one-row seam
prices and Proposition 2's conditional summable-seam certificate adapter,
including unrestricted behavioral caps through the semantic-pair cap
coordinate and generated secants.

**Not proved:** the summable seam selection from actual atom/reset data; the
small initial candidate-debt block chain; the mover-singleton second clock;
any new Lean declaration; or the finite-quitting uniform-equilibrium
conjecture.

**Independent review.**  Gauss validated Proposition 1 and the first
version's seam/secant/suffix algebra, while identifying its circular actual-
semantic initial condition, in
[`feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_GAUSS.md`](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_GAUSS.md).
That objection is incorporated by the revised nonsemantic-candidate item 1.
Gauss then checked the revision, including arbitrary ambient candidate pairs,
generated-secant orientation, boundedness, and all remaining certificate
fields, in
[`feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_GAUSS__ROUND_2.md`](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_GAUSS__ROUND_2.md).
Noether independently checked the same repaired theorem, including the
max-branch switch, actual-versus-candidate secant orientation, artificial
small debt, and every certificate field, in
[`feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER.md`](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER.md).

## 8. Semantic rigidity and the unavoidable seam toll

The artificial candidate annotations in Proposition 2 avoid assuming an
actual nearly Nash source.  They cannot, however, evade the semantic endpoint
once the literal clocks forget every bounded boundary condition.

Write the concatenated global candidate sequence as

\[
 X_t=(u_t,b_t),
\]

and let `q_t` be its literal root.  At internal rows

\[
 X_t=F_{q_t}(X_{t+1}).                                  \tag{8.1}
\]

At a seam after block `k`, the inherited current candidate was computed using
the donated endpoint `X_{k,N_k}`, whereas the actual next global candidate is
`X_{k+1,0}`.  Proposition 1 therefore bounds the global Bellman residual at
that row by

\[
 |e^u_{t,i}|\le A_{k,i},\qquad
 |e^b_{t,i}|\le B_{k,i};                                \tag{8.2}
\]

all other residuals being zero.

Let `Sigma^t=(U_t,B_t)` be the actual terminal semantic pair of the infinite
product-root tail beginning at time `t`.  It obeys the exact Bellman identity

\[
 \Sigma^t=F_{q_t}(\Sigma^{t+1}).                         \tag{8.3}
\]

Here `B_t` is the unrestricted behavioral best-response cap, not a one-shot
surrogate.

### Proposition 3 (bounded Bellman-chain semantic rigidity)

Assume the candidate prescribed values and debts are uniformly bounded and
nonnegative.  Assume joint survival and every player-deleted survival of the
literal roots vanish on every suffix.  Then, for each player `i`,

\[
 |U_0(i)-u_0(i)|\le \sum_k A_{k,i},                      \tag{8.4}
\]

\[
 |B_0(i)-b_0(i)|\le \sum_k B_{k,i},                      \tag{8.5}
\]

and consequently

\[
 |(B_0-U_0)(i)-(b_0-u_0)(i)|
 \le \sum_k(A_{k,i}+B_{k,i}).                           \tag{8.6}
\]

In particular, a zero-seam bounded Bellman chain is exactly the actual
terminal semantic pair of its infinite literal root profile.

#### Proof

Let `J_t` be the all-player Continue mass of `q_t` and `O_{t,i}` its
player-`i`-deleted Continue mass.  Subtracting (8.3) from the candidate
recursion with residual gives

\[
 |u_t(i)-U_t(i)|
 \le |e^u_{t,i}|+J_t|u_{t+1}(i)-U_{t+1}(i)|.             \tag{8.7}
\]

The cap prefix is the maximum of a tail-independent forced-Quit value and an
affine Continue value with successor coefficient `O_{t,i}`.  Its
`O_{t,i}`-Lipschitz property gives

\[
 |b_t(i)-B_t(i)|
 \le |e^b_{t,i}|+O_{t,i}|b_{t+1}(i)-B_{t+1}(i)|.         \tag{8.8}
\]

Iterating to a finite horizon `T` weights each earlier residual by a product
of Continue masses, hence by a number in `[0,1]`.  The terminal remainder in
(8.7) is joint survival through `T` times a uniformly bounded difference;
the remainder in (8.8) is player-deleted survival times a uniformly bounded
difference.  Actual payoffs and deviation caps are bounded by the reward
bound, while candidate caps are bounded because `b=u+(b-u)`.  Both remainders
therefore tend to zero.  Only seams have nonzero residuals, so (8.4)--(8.5)
follow.  The triangle inequality gives (8.6).

### Corollary 3A (positive-minimum seam toll)

Suppose `Delta>0` is a global lower bound for total debt on the actual terminal
semantic carrier:

\[
 \Delta\le \sum_i (B-U)(i)                               \tag{8.9}
\]

for every executable profile.  Any bounded candidate Bellman chain satisfying
the clock hypotheses of Proposition 3 must obey

\[
 \Delta
 \le \sum_i\left[(b_0-u_0)(i)
       +\sum_k(A_{k,i}+B_{k,i})\right].                 \tag{8.10}
\]

In particular, the hypotheses of Proposition 2 imply

\[
 \Delta\le 2|I|\eta.                                    \tag{8.11}
\]

#### Proof

The actual concatenated root profile belongs to the terminal semantic
carrier, so (8.9) applies to `(U_0,B_0)`.  Candidate debt is nonnegative, and
(8.6) gives coordinatewise

\[
 (B_0-U_0)(i)
 \le (b_0-u_0)(i)+\sum_k(A_{k,i}+B_{k,i}).
\]

Summing proves (8.10); Proposition 2 bounds both displayed contributions for
each player by `eta`, proving (8.11).

### Consequence for the producer

The zero-seam shortcut is closed: choosing arbitrary bounded annotations and
then finding an exact invariant Bellman orbit with the required clocks would
already produce an actual zero-debt terminal profile.  More generally, in the
positive-minimum contradiction branch the source geometry must genuinely pay
down the fixed toll `Delta`; compact recurrence of annotations alone cannot
make the seam budget vanish.  The live question is therefore one-sided and
quantitative: which atom/reset forcing identity makes the total seam toll
smaller than the positive carrier minimum while retaining the actual clock
charge?

Proposition 3 and Corollary 3A are ordinary mathematics.  Noether
independently reconstructed the unrestricted behavioral-cap recursion,
nonattained-supremum/max-switch cases, both clock-weighted boundary
remainders, and the `2|I|eta` constant in
[`feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_2.md`](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_2.md).

## 9. Signed seams: cap drops are favorable forcing

Proposition 2 bounded every seam by absolute cap displacement.  Proposition
3 shows why demanding those absolute displacements tend to zero is already
an endpoint-strength obligation.  The chronological consumer is one-sided,
so the correct seam datum retains the sign.

Fix the last root `q` of one block and player `i`.  Write its cap prefix as

\[
 H_i(z)=\max\{Q_i,\ C_i+O_i z\},                         \tag{9.1}
\]

where `Q_i` is the forced-Quit value, `C_i` is the absorbing part of forced
Continue, and `O_i` is opponent Continue mass.  Let `J` be joint Continue
mass.  Suppose the block was computed with donated successor

\[
 Y^-=(u^-,b^-),
\]

but the next global block begins with candidate pair

\[
 Y^+=(u^+,b^+).
\]

The annotated current pair is `F_q(Y^-)`, while the global template at this
row is `F_q(Y^+)`.

### Proposition 4 (exact signed seam identity)

With the project's direct-defect orientation

```text
annotated current debt - global-template prefix debt,
```

the prescribed and direct-debt seam defects are exactly

\[
 P_i=J(u^-_i-u^+_i),                                    \tag{9.2}
\]

\[
 E_i=H_i(b^-_i)-H_i(b^+_i)-P_i.                         \tag{9.3}
\]

If `b^-_i>=b^+_i`, then

\[
 H_i(b^-_i)-H_i(b^+_i)\ge0,
 \qquad
 (-E_i)_+\le(P_i)_+\le |P_i|
          \le J|u^-_i-u^+_i|.                           \tag{9.4}
\]

If the Continue branch is active at both cap arguments, its contribution is
exactly

\[
 H_i(b^-_i)-H_i(b^+_i)=O_i(b^-_i-b^+_i).                \tag{9.5}
\]

If the forced-Quit branch is active at both, the contribution is zero.  At a
branch switch it is the corresponding truncated amount between zero and the
right side of (9.5).

#### Proof

The prescribed prefix depends on its successor only through `J u_i`, giving
(9.2).  The two annotated debts are cap minus prescribed payoff, so
subtracting them gives (9.3).  The function `H_i` is nondecreasing because
`O_i>=0`.  Therefore a donated-to-next cap drop makes the first difference in
(9.3) nonnegative, and

\[
 -E_i=P_i-[H_i(b^-_i)-H_i(b^+_i)]\le P_i.
\]

Taking positive parts proves (9.4).  The two affine/constant branch formulas
give (9.5) and the stated boundary cases.

### Corollary 4A (one-sided cap-drop seam adapter)

Retain items 1, 2, and 4 of Proposition 2.  Replace its absolute seam budget
by the following conditions for every player `i`:

\[
 \sum_k |u_{k,N_k,i}-u_{k+1,0,i}|\le\eta,               \tag{9.6}
\]

\[
 b_{k,N_k,i}\ge b_{k+1,0,i}\quad\text{for every }k.     \tag{9.7}
\]

Then the same literal roots and candidate annotations give a
`QuittingChronologicalDebtShadowingCertificate reward eta`.  No summability
or smallness assumption on the cap drops is required.

More generally, it is enough that the total cap-order violation

\[
 \sum_k (b_{k+1,0,i}-b_{k,N_k,i})_+                     \tag{9.8}
\]

plus the prescribed budget in (9.6) is at most `eta`; the cap-rise term may
be sharpened by the actual seam coefficient `O_i`.

#### Proof

The prescribed discrepancy on every finite suffix is bounded by the subset
sum of (9.6), since its seam term has absolute value `J` times the displayed
difference and `0<=J<=1`.

For the adverse forcing term, let `w_{k,i}` be the generated-secant survival
weight reaching a seam.  It lies in `[0,1]`.  Under (9.7), Proposition 4 gives

\[
 -w_{k,i}E_{k,i}
 \le w_{k,i}(-E_{k,i})_+
 \le |P_{k,i}|
 \le |u_{k,N_k,i}-u_{k+1,0,i}|.                         \tag{9.9}
\]

Summing over any finite suffix proves the required bound, uniformly in its
length; the eventual slack clause is automatic.  Every other certificate
field is unchanged from Proposition 2.

If (9.7) fails, monotonicity and the `O_i`-Lipschitz bound give

\[
 (-E_i)_+
 \le |P_i|+O_i(b^+_i-b^-_i)_+,                          \tag{9.10}
\]

which proves the generalized statement.

### Exact source-facing residual

Corollary 4A is strictly weaker than absolute seam matching.  It permits the
positive toll from Corollary 3A to be realized by large **favorable** cap
drops, repeatedly replenished by exact Bellman motion inside the donated
blocks.  It also identifies two real failure modes.

1. A nominal cap drop entirely below the forced-Quit floor has no favorable
   effect: `H_i` is constant there.
2. A simultaneous prescribed drop can cancel the cap effect through the
   exact `-P_i` term.

The next actual-data check is therefore narrower than (0.1): can the
atom/reset replacement be oriented so that its donated endpoint cap dominates
the next source cap in every coordinate, with summable prescribed mismatch,
while the interior Bellman block restores enough cap height to repeat the
drop and carries the two literal clocks?  A mover-only debt reduction does
not by itself imply this coordinatewise cap order, so no source adapter is
claimed yet.

Proposition 4 and Corollary 4A are ordinary mathematics.  Noether
independently checked the defect orientation, max-switch truncation, cap-rise
term, and every-finite-suffix weighted estimate in
[`feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_3.md`](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_3.md).

## 10. The own-replacement conservation law

The positive-minimum tangent data replace one mover's behavioral strategy
while leaving every opponent strategy fixed.  For that mover, this operation
cannot create the cap drop required by Corollary 4A.

### Proposition 5 (own replacement pairs forcing with prescribed drift)

Let `sigma` be any complete behavioral profile, let player `i` replace only
their own strategy, and write the resulting profile as `tau`.  Denote their
terminal semantic coordinates by

\[
 (U^\sigma_i,B^\sigma_i),\qquad
 (U^\tau_i,B^\tau_i).
\]

Then

\[
 B^\sigma_i=B^\tau_i,                                  \tag{10.1}
\]

and hence

\[
 d^\sigma_i-d^\tau_i=U^\tau_i-U^\sigma_i.              \tag{10.2}
\]

Use these two semantic pairs as the donated and next successors at an
arbitrary bridge root `q`, in the orientation `sigma -> tau`.  Its mover-`i`
seam defects satisfy

\[
 P_i=J(U^\sigma_i-U^\tau_i),                            \tag{10.3}
\]

\[
 E_i=-P_i
     =J(d^\sigma_i-d^\tau_i).                           \tag{10.4}
\]

Thus whenever the replacement lowers mover debt, the direct-debt defect is
favorable, but its magnitude is exactly the magnitude of the simultaneous
prescribed defect.  This conclusion also holds for every partial mixture of
the mover's source and replacement stopping laws.

#### Proof

The continuation best-response cap for player `i` is the supremum over their
own behavioral strategies against the fixed opponent profile.  It is
therefore invariant under changing which one of player `i`'s strategies is
designated as prescribed, proving (10.1).  Subtracting `d=B-U` gives (10.2).

In Proposition 4's notation, the successor cap arguments are equal.  Hence
`H_i(B^\sigma_i)-H_i(B^\tau_i)=0`, so (9.3) gives `E_i=-P_i`.
Equation (10.2) gives the second equality in (10.4).  A behavioral mixture
still changes only player `i`'s prescribed strategy and leaves the opponent
law, hence the cap, fixed.

### Consequence for atom/reset chronology

The mover's low-debt full replacement is not a free one-sided seam.  At reset
scale `lambda`, its useful forcing and its prescribed mismatch are the same
first-order quantity.  If such same-orientation seams carry a nonsummable
clock/reset charge, their absolute prescribed mismatches are nonsummable as
well, so Corollary 4A does not apply.

The literal certificate permits signed prescribed cancellation, but returning
from `tau` to `sigma` through the same cap-invariant seam reverses (10.3)--
(10.4): it cancels the prescribed residual and repays the favorable forcing
as an equally adverse defect.  Therefore a two-state source/replacement
toggle has zero net mover ledger.

A viable producer must break this conservation in one of two ways.

1. **Cross-player cap pump:** while another player's strategy moves, player
   `i`'s opponent law changes, allowing a cap drop to pay the prescribed
   return without an adverse mover defect.
2. **Exact Bellman return:** an executable interior block restores the source
   payoff/cap through its root dynamics rather than through a reverse seam.

This is the source-matched residual behind Section 9.  The static tangent
family supplies an own replacement and an atom observed in another
coordinate, but it does not yet supply either a closed cross-player cap pump
or an exact Bellman return.  Proposition 5 is ordinary mathematics.  Noether
independently checked cap invariance for nonattained suprema and partial
mixtures, the exact sign identity, and same-root conservation in the Round 3
feedback linked above.

## 11. A balanced small shuttle pays every suffix

Conservation of the unweighted mover ledger does not itself rule out a
chronological certificate.  The certificate allows error `eta` on every
suffix, and its direct forcing is weighted by a nonincreasing product of
secants.  A uniformly small alternating shuttle fits those quantifiers
exactly.

### Proposition 6 (alternating-seam forcing lemma)

Fix a player `i`.  Suppose all internal row defects vanish and the nonzero
seam defects, in chronological order, obey

\[
 P_{k,i}=(-1)^k p_i,
 \qquad
 E_{k,i}=-P_{k,i},                                      \tag{11.1}
\]

up to reversing the initial phase, for one constant

\[
 0\le p_i\le\eta.                                       \tag{11.2}
\]

Assume all generated secants lie in `[0,1]`.  Then:

1. every finite calendar interval has absolute total prescribed defect at
   most `eta`; and
2. every finite calendar interval has survival-weighted adverse direct
   forcing at most `eta`.

Consequently, if (11.1)--(11.2) hold for every player and the candidate
boundedness, nonnegative debt, small initial debt, generated-secant, and
literal clock hypotheses also hold, the data form a full chronological
debt-shadowing certificate at accuracy `eta`.

#### Proof

An arbitrary calendar interval contains a consecutive finite subsequence of
the seam list, with zeros between seams.  A finite sum of consecutive terms
from the alternating sequence `+p_i,-p_i,+p_i,...` is `0`, `p_i`, or `-p_i`.
This proves the prescribed bound.

For the direct term, fix a calendar start and list the seam dates it reaches.
Let `w_k` be the secant-survival product from that start to seam `k`.  Since
each intervening secant lies in `[0,1]`,

\[
 1\ge w_0\ge w_1\ge w_2\ge\cdots\ge0.                  \tag{11.3}
\]

After factoring out `p_i`, every finite weighted direct sum is an alternating
sum of a nonincreasing nonnegative sequence.  If its first sign is positive,
pairing gives a value in `[0,w_0]`.  If its first sign is negative, pairing
gives a value in `[-w_0,0]`.  In particular it is always at least `-w_0`,
hence at least `-1`.  Therefore

\[
 -\sum_k w_k E_{k,i}\le p_i\le\eta.                     \tag{11.4}
\]

This is stronger than the eventual `eta+slack` requirement.

### Application and exact remaining construction

For one own-strategy source/replacement pair, Proposition 5 gives `E=-P`.
Using the same bridge root in both orientations makes the two magnitudes
equal.  Choosing a sufficiently small partial-reset scale can make that
common magnitude at most `eta`.  Thus the **analytic** prescribed/forcing
ledger of an alternating source--replacement shuttle is sound; its zero net
unweighted forcing is not an obstruction.

What is not supplied by the static tangent data is the shuttle itself.  The
successor after a literal source block is its reached tail, not an
independently selected replacement semantic pair, and the successor after the
replacement block is not automatically the original source.  Repeating the
two labels or concatenating the two donated profiles does not prove the exact
Bellman identities at those seams.  Moreover one mover's low replacement debt
does not make every player's initial candidate debt small.

The surviving positive target is therefore precise:

> Construct, at every `eta`, an actual bounded Bellman block shuttle whose
> seam pairs alternate between source and partial replacement with matched
> defect amplitudes at most `eta`, whose initial candidate debt is small in
> every coordinate, and whose literal roots carry the required clocks.

Failure of exact reached-tail return, not the alternating forcing algebra, is
the current blocker.  Proposition 6 is ordinary mathematics.  Noether
independently checked arbitrary calendar starts and finite horizons and the
monotone alternating-weight bound in
[`feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_4.md`](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_4.md).

## 12. A scale-free normalized incentive compiler

The exact Nash--Bellman spine audit suggests a different repair.  Exact root
Nash gives zero candidate debt but may select roots with no persistent clocks.
Instead of splicing unrelated clock blocks, retain exact Bellman evaluation
and allow a controlled root Nash gap paid by the opponents' actual one-row
absorption.

Let `v_t` be uniformly bounded payoff vectors and `q_t` literal product
roots satisfying exact prescribed Bellman recursion

\[
 v_t=\operatorname{SuccPayoff}(q_t,v_{t+1}).             \tag{12.1}
\]

For player `i`, define the diagonal-tail root Nash gap

\[
 g_{t,i}:=d_i\bigl(F_{q_t}(v_{t+1},v_{t+1})\bigr)\ge0.  \tag{12.2}
\]

Write `O_{t,i}` for the probability that all opponents of `i` Continue at
root `q_t`.

### Proposition 7 (opponent-absorption-normalized incentive compiler)

Assume `eta>0`, the literal roots have vanishing joint and every-player-
deleted survival on every suffix, and

\[
 g_{t,i}\le\eta(1-O_{t,i})                               \tag{12.3}
\]

for every date and player.  Then the diagonal candidate data

```text
prescribed(t)=v_t,
debt(t)=0,
```

with generated secants against the literal executable tails form a
`QuittingChronologicalDebtShadowingCertificate reward eta`.

#### Proof

Boundedness and nonnegative candidate debt are immediate, and initial
candidate debt is zero.  Equation (12.1) makes every prescribed defect zero.
With the direct-defect orientation of Proposition 4, diagonal candidate debt
zero gives

\[
 E_{t,i}=-g_{t,i}.                                      \tag{12.4}
\]

Let `s_{t,i}` be the generated cap secant.  It satisfies

\[
 0\le s_{t,i}\le O_{t,i}\le1.                           \tag{12.5}
\]

For a suffix starting at `m`, put

\[
 w_0=1,
 \qquad
 w_{n+1}=w_n s_{m+n,i}.                                 \tag{12.6}
\]

Then (12.3)--(12.5) give

\[
 w_n g_{m+n,i}
 \le\eta w_n(1-O_{m+n,i})
 \le\eta w_n(1-s_{m+n,i})
 =\eta(w_n-w_{n+1}).                                    \tag{12.7}
\]

Therefore every finite adverse sum telescopes:

\[
 -\sum_{n<L}w_nE_{m+n,i}
 =\sum_{n<L}w_ng_{m+n,i}
 \le\eta(1-w_L)\le\eta.                                \tag{12.8}
\]

The prescribed discrepancy is identically zero, the generated-secant fields
hold by construction, and the assumed literal clocks supply both survival
fields.  These are all certificate fields.

### Why scaling one hazard is insufficient

Condition (12.3) is scale-free in the hard direction.  Suppose player `i`
strictly prefers Continue to Quit by action gap `a_i>0` at a root and is
assigned a small own Quit hazard `delta`.  Holding the opponent law fixed,
their mixed-action regret is `delta a_i`.  But their own hazard does not
change `1-O_i`, which depends only on opponents.  Thus shrinking `delta`
does not by itself pay player `i`'s error.

If two players `i,j` are doped at comparable hazards, each can pay the other's
clock only when their action gaps are themselves `O(eta)` (with the exact
hazard-ratio constants).  In particular, a strict inactive-action gap cannot
be overcome merely by making both hazards rare: regret and opponent
absorption are both first order in the doping scale, so their ratio stays
positive.

This identifies the new producer datum:

> At every accuracy, construct a bounded exact Bellman spine with two
> persistent labelled hazards such that every player's diagonal root Nash
> gap is at most `eta` times that player's opponent absorption probability.

An exact Nash--Bellman spine is the zero-gap special case, but arbitrary
compact selection may choose the all-Continue phantom.  Atom blocks provide
clock incidence but are not currently shown to satisfy the normalized
incentive ratio against one common Bellman continuation.  The unresolved step
is therefore a cross-player near-indifference gadget, not a smaller hazard
scale.

Proposition 7 is ordinary mathematics.  Gauss independently checked the
root-gap/direct-defect sign, max-switch secant, zero-denominator boundary,
telescoping constant, and complete certificate field list in
[`feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_GAUSS__ROUND_3.md`](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_GAUSS__ROUND_3.md).
Noether independently checked the same diagonal-gap and every-suffix argument,
including the binding `O=1` boundary, in
[`feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_5.md`](../feedback/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION__BY_CODEX_NOETHER__ROUND_5.md).

## 13. Strict Continue blocks rare-hazard doping

The normalized ratio (12.3) cannot be forced merely by taking every Quit
probability smaller.  The obstruction is already one-row and exact.

### Proposition 8 (uniform strict-Continue obstruction)

Let the finite player set have cardinality `n>=2`.  At one product root `q`,
write

\[
 p_i=\Pr_q(i\text{ Quits}).
\]

Against diagonal continuation `v`, suppose every player strictly prefers
Continue to Quit by at least `a>0`, with the opponents held at `q_{-i}`.  If
the normalized incentive inequalities

\[
 g_i\le\eta(1-O_i)                                      \tag{13.1}
\]

hold for every player and

\[
 \eta<{a\over n-1},                                     \tag{13.2}
\]

then `p_i=0` for every player.

#### Proof

Since Continue is the better pure action by at least `a`, mixing Quit with
probability `p_i` loses at least `a p_i` relative to the best action.  Hence

\[
 a p_i\le g_i.                                          \tag{13.3}
\]

The finite union bound gives

\[
 1-O_i\le\sum_{j\ne i}p_j.                              \tag{13.4}
\]

Combining (13.1)--(13.4) and summing over `i` yields

\[
 a\sum_i p_i
 \le\eta\sum_i\sum_{j\ne i}p_j
 =\eta(n-1)\sum_i p_i.                                  \tag{13.5}
\]

Under (13.2), this forces `sum_i p_i=0`; nonnegativity gives every `p_i=0`.

For one player, the same conclusion holds directly whenever Continue is
strictly better: opponent absorption is zero, so (13.1) forces `g_i=0` and
hence `p_i=0`.

### Consequence for the actual atom words

At arbitrarily small certificate accuracy, a clock-carrying normalized-
incentive root must therefore contain a player who is nearly indifferent or
weakly favors Quit; a root on which every player has a fixed strict Continue
margin cannot carry any hazard.  With two rare doped labels, their own regret
is first order in their own hazard while the right side is first order in the
other labels' hazards, so comparable shrinking cancels out of the ratio.

Cedar Proposition 5 supplies two co-realized raw hazard quotas in most atom
branches, but it gives no action-gap estimate for the second label against one
common diagonal Bellman continuation.  The same-profile moving-row estimate
controls one displayed owner and is survival-weighted; it is not the
playerwise pointwise ratio (12.3).  Thus existing atom incidence does not yet
instantiate Proposition 7.

The hard positive question is now finite-dimensional and source-facing:
does positive-minimum atom access force a clock-rich row/short block on which
every hazard-carrying strict-Continue gap is `o(opponent absorption)`, or does
failure of that condition feed one of the existing exact endpoint branches?

Proposition 8 is ordinary mathematics and has not yet been independently
reviewed.

## 14. Clean stopping boundary

### Proved and independently reviewed

- Propositions 1--2: exact seam prices and the nonsemantic summable-seam
  certificate adapter.  Gauss and Noether independently checked the repaired
  arbitrary-candidate formulation.
- Proposition 3 and Corollary 3A: bounded Bellman-chain semantic rigidity and
  the positive-minimum seam toll.  Noether independently checked unrestricted
  cap recursion and the exact constant.
- Proposition 4 and Corollary 4A: signed cap-drop forcing.  Noether checked
  the direct-defect sign, max switches, and every-suffix estimate.
- Proposition 5: own-strategy replacement conserves the mover cap and pairs
  favorable forcing with prescribed drift.  Noether checked nonattained caps,
  mixtures, and reversal.
- Proposition 6: alternating small shuttles satisfy both analytic forcing
  accounts.  Noether checked arbitrary starts and finite horizons.
- Proposition 7: opponent-absorption-normalized root regret telescopes to a
  full chronological certificate.  Gauss and Noether independently checked
  every field and the boundary `O_i=1`.

### Proved but not independently reviewed

Proposition 8 is elementary one-row algebra: a uniform strict Continue margin
`a` and the normalized incentive inequalities force all hazards to vanish
when `eta<a/(|I|-1)`.  No stronger source consequence is inferred from it.

### Exact remaining gap

For every `eta>0`, construct from the arbitrary finite quitting-game data a
bounded pair of sequences

\[
 v:\mathbb N\to\mathbb R^I,
 \qquad
 q:\mathbb N\to\prod_i\Delta\{C,Q\},
\]

such that:

1. `v_t` is the exact prescribed Bellman evaluation of `q_t` against
   `v_{t+1}`;
2. for every player and date, the diagonal-tail root Nash gap satisfies
   `g_{t,i}<=eta(1-O_{t,i})`; and
3. two distinct fixed labels have divergent cumulative marginal Quit hazard.

Items 1--3 are the whole unproved producer.  Proposition 7 supplies all
remaining candidate, forcing, secant, survival, and small-initial-debt fields.

The smallest decisive next check is source-specific: at a clock-carrying atom
row, compute the action gap of the **second** hazard label against the same
diagonal continuation used for the mover.  If its gap is not
`o(opponent absorption)`, determine whether that strict sign produces an
existing sure-exit/solo endpoint.  Current atom access supplies raw incidence
and a moving-row estimate for one owner, but no common-continuation bound for
this second action gap.

No unconditional producer, full conjecture proof, or new checked theorem is
claimed, and nothing in this notebook meets the export gate by itself.
