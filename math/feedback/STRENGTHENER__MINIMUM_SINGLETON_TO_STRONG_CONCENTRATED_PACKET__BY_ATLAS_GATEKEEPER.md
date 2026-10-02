# Audit of minimum-singleton to strong concentrated packet

Reviewer: `ATLAS_GATEKEEPER`

## Revised verdict after the arbitrary-observer repair

**EXPORT in a corrected, stronger form.**  The inactive-owner premise in the
review below is unnecessary.  It entered only because the original argument
used the terminal gap to select a profitable player different from the
singleton owner.  Instead, fix *any* player `o != j` (possible on `Fin 4`) and
replace `o` by an `e_n`-near-best pure quitting time.  The replacement itself
makes `o`'s full behavioral debt at most `e_n`; no premise on the old debt of
`j` or `o`, and no terminal exploitability witness, is needed.

In fact the minimum-law and clock-compression hypotheses are also unnecessary
for the local theorem.  **Any one actual profile carrying one positive
singleton stage atom** produces an actual
`QuittingReprojectionConcentratedPacket` by this construction.  Therefore it
applies uniformly to the minimum-law owner-clock origin and to both existing
reached-singleton origins.  It unifies all three Fin4 singleton origins behind
the maintained recurrent concentrated-packet interface.  This strictly
narrows `questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md` to consumption of that
one packet type, while also giving the concentration output requested by
`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`.  It does not consume the
resulting packet.

The original note must be rewritten around the stronger statement before
export.  The conditional proof audited below remains correct but is no longer
the maximal result.

## Final strengthening: one exact same-stage endpoint suffices

The pure-time approximation argument above is itself unnecessarily weak.
There is an exact, tail-preserving construction already supported by the
same-stage endpoint API.

Start from one actual profile `tau` with a positive nonempty coalition `S` at
date `t`, and fix an owner `o` such that `S != {o}`.  (For the singleton
application, `S={j}` and this is exactly `o != j`.)  Let `a` be

```text
quittingRootBestEndpointAction reward tail root o
```

for the literal tail and root at date `t`, and let `rho` be the literal
one-date profile obtained by replacing only `o`'s date-`t` action by the pure
action `a`.  Then:

1. `rho` has exactly the same complete live-root past before `t` and the same
   complete live-root tail after `t` as `tau`;
2. the marked atom is routed to `S.erase o` or `insert o S`, according to the
   pure action, with no loss of stage mass, by
   `quittingRootCoalitionMass_le_pureEndpointRouted` and preservation of live
   mass; the assumption `S != {o}` makes either routed set nonempty;
3. the coordinate Nash defect of `o` at the new root is exactly zero, because
   `o` now assigns probability one to a maximizing endpoint and its two
   endpoint values are unchanged when only its own marginal is replaced.

For completeness, write
`Delta = QuitPayoff_o - ContinuePayoff_o`.  The checked identity
`quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` is

\[
 d_o^{\rm root}
 =p_o(C)(\Delta)_+ + p_o(Q)(-\Delta)_+.
\]

`quittingRootBestEndpointAction` chooses Continue when `Delta <= 0` and Quit
when `Delta > 0`.  The endpoint difference is invariant under updating `o`'s
own marginal (`quittingRootEndpointDifference_update_ownMarginal`, or the
equivalent self-update lemma).  Substitution of the corresponding pure
probabilities therefore makes both terms zero.  This covers ties as well.

Repeat the single profile `rho` as a constant sequence, take any positive
scale tending to zero, constant mark `t`, constant cutoff `t+1`, and the
identity subsequence.  The normalized-defect field is identically zero.
Positive routed stage mass gives the literal semantic-prefix field.  This is
a `QuittingReprojectionConcentratedPacket` with stronger provenance than the
pure-time construction: there is no finite-mode subsequence and no loss of
the original post-date tail.

Accordingly the **preferred export statement** is:

> For every finite quitting game, every actual positive stage atom `S`, and
> every player `o` with `S != {o}`, one literal best-endpoint update of `o`
> has a nonempty routed atom of no smaller mass; its constant repetition is a
> `QuittingReprojectionConcentratedPacket` with owner `o`, and the complete
> past and tail are unchanged.

The Fin4 atlas corollary applies this theorem to every
`FinFourAtlasWeakConcentratedSingletonCore`.  Hence all three singleton origins
reach the same recurrent packet interface while retaining their origin data.

The generic statement also packetizes nonsingleton monodromy rows, but that is
not an atlas contraction: the current collision consumer can route its
remaining other-player defect straight back into the same horizontal toggle
dynamics.  This circular application is not part of the conjecture-facing
claim.

This strengthening uses existing local lemmas but the **adapter to the packet
type is fresh**: the repository has no constructor from an arbitrary positive
singleton stage atom to `QuittingReprojectionConcentratedPacket`.  In
particular,
`quittingTerminalPayoff_stageBestEndpointDeviation_markedRouting` additionally
assumes a strictly positive old defect because it needs a profitable global
deviation; the present packet producer needs only the unconditional mass
routing lemma and exact zero defect at the updated root.

The narrow Lean handoff should use:

- `quittingLiteralOneDateProfile` and
  `quittingProfileLiveRoot_literalOneDateProfile`;
- `quittingLiveMass_literalOneDateProfile_eq` and
  `quittingProfileLiveRoot_literalOneDateProfile_tail_eq`;
- `quittingRootCoalitionMass_le_pureEndpointRouted`;
- `quittingRootEndpointDifference_update_ownMarginal` and
  `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`; and
- `positive_stageCoalitionMass_has_semanticPrefixIncidence`.

The first three live in the checked same-stage endpoint/routing modules; the
last semantic incidence is in
`TerminalSemanticPlateauIncidence.lean`.  No best-response supremum,
stopping-law compactness, Green telescope, or terminal witness is needed in
this preferred proof.

The earlier pure-time repair remains mathematically correct and may be useful
when a global near-cap profile is specifically wanted, but it should not be
the main exported theorem or Lean handoff.

## Earlier pure-time formulation (valid but superseded)

Let `iota` be a finite player type with distinct players `j,o`.  Let `tau` be
one arbitrary behavioral profile, let `t : Nat`, and let `terminal` be the
singleton `{j}`.  Assume

\[
 0<\lambda\le
 \Pr_{\tau}(\text{terminal is }\{j\}\text{ at date }t).
\]

Then there are actual profiles `rho_n`, positive scales `s_n -> 0`, a fixed
nonempty terminal `S`, cutoffs, and a `QuittingReprojectionConcentratedPacket`
with owner `o`, resolution `lambda`, and profiles `rho_n`.  Every `rho_n` is a
literal pure-time update of the **same** source `tau` at coordinate `o`.

More precisely, take `s_n=1/(n+1)`, choose `q_n : Option Nat` within `s_n^2`
of `o`'s behavioral cap against `tau`, and put
`rho_n=tau[o <- Q(q_n)]`.  After a strictly increasing subsequence exactly one
of the three routing forms displayed below is fixed, the routed atom has mass
at least `lambda`, and

\[
 \frac{\operatorname{Live}_{\rho_n}(h_n)
              \operatorname{Defect}_o(\rho_n,h_n)}{s_n}\longrightarrow0.
\]

One may take the constant cutoff `t+1`: in the early mode `h_n=q_n<t`, while
in the equal and late modes `h_n=t`.  Thus there is no hidden moving-cutoff or
finite-deadline premise.

## Fin4 minimum-source corollary

Let `source : FinFourMinimumAtomProducer reward bound`, and suppose its
selected terminal has cardinality one.  Unpack
`source.nonempty_ownerCompressedSingletonProducer` as a fixed singleton owner
`j`, one fixed minimum-source chronology, and cofinally deep compressed
endpoints.  Put

\[
 \lambda=\frac{\mu^2}{8}>0,
 \qquad
 \mu=\text{the selected minimum-law singleton mass}.
\]

Then one may choose:

- a fixed player `o != j`;
- for every `n`, one owner-compressed endpoint `tau_n` requested beyond depth
  `n`, with marked date `t_n` and singleton `{j}` mass `> lambda`;
- `s_n=1/(n+1)` and a pure time `q_n : Option Nat` whose payoff for `o`
  against `tau_n` is at least `B_o(tau_n)-s_n^2`; and
- the actual profile
  `rho_n = tau_n[o <- quittingPureTimeBehaviorStrategy o q_n]`.

After a strictly increasing subsequence, one of the following three routing
modes is fixed:

\[
\begin{array}{c|c|c}
q_n=\infty\text{ or }t_n<q_n & h_n=t_n & S=\{j\},\\
q_n=t_n & h_n=t_n & S=\{j,o\},\\
q_n<t_n & h_n=q_n & S=\{o\}.
\end{array}
\]

Along that subsequence,

\[
 \Pr_{\rho_n}(S\text{ at }h_n)>\lambda,
 \qquad
 \frac{\operatorname{Live}_{\rho_n}(h_n)
              \operatorname{Defect}_o(\rho_n,h_n)}{s_n}\longrightarrow0.
\]

Consequently the reindexed profiles, owner `o`, fixed terminal `S`, cutoffs
`h_n+1`, and scale `s_n` instantiate
`QuittingReprojectionConcentratedPacket` with resolution `lambda`.  A dependent
adapter should retain the original `source`, producer, chronology, chosen
compressed endpoints, pure times, and the literal equality defining each
`rho_n`; these data certify actual-source provenance even though the update is
not tail-preserving.

## Proof of the repair

Choose `o != j` once.  The checked approximate pure-time theorem
`exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub` gives `q_n` for
the positive error `s_n^2`.  The cap of `o` depends only on its opponents, so
`quittingContinuationBestResponseValue_update_self` gives

\[
 0\le d_o(\rho_n)\le s_n^2.
\]

This is the sole small-debt input used by the Green estimate.  It is created
at the target and need not be present at the minimum source.

On the source event `{j}` at `t_n`, player `o` survives through `t_n`.
Independence of the live-path product laws gives the three exact comparisons:

1. if `q_n` is later or `Never`, deleting `o`'s old survival factor preserves
   `{j}` at `t_n` with at least the old mass;
2. if `q_n=t_n`, it routes the event to `{j,o}` at `t_n` with at least the old
   mass; and
3. if `q_n<t_n`, the old event implies that every opponent of `o` survives
   through `q_n`, so the update produces `{o}` at `q_n` with at least the old
   mass.

The three modes form a finite partition, including the `Option Nat = none`
case in the first mode.  Infinite pigeonhole therefore supplies a strictly
increasing subsequence with fixed mode and terminal.  One can either retain
that subsequence in the packet, or reindex and use the identity subsequence.
No deadline compactness is being assumed.

Finally,

\[
 \operatorname{Live}_{\rho_n}(h_n)
 \operatorname{Defect}_o(\rho_n,h_n)
 \le d_o(\rho_n)\le s_n^2
\]

by `quittingLiveMass_mul_coordinateNashDefect_le_initialDebt`.  Division by
`s_n>0` gives a bound by `s_n`, hence the required limit.  Positive stage mass
supplies `semanticPrefix` through
`positive_stageCoalitionMass_has_semanticPrefixIncidence`.

## Exact API and freshness audit for the corrected result

The arbitrary-source entrance is checked in
`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`:

- `FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer`;
- `FinFourOwnerCompressedSingletonProducer.cofinal_endpoint`;
- `FinFourOwnerCompressedSingletonEndpoint.target_stageMass_gt`; and
- the retained source chronology and source-only stack fields on the same
  endpoint.

The output API is the structure
`QuittingReprojectionConcentratedPacket` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`.
Its required semantic incidence and normalized-defect tools are exactly
`positive_stageCoalitionMass_has_semanticPrefixIncidence` and
`quittingLiveMass_mul_coordinateNashDefect_le_initialDebt`.

The approximate pure-time selector is already checked as
`exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub` in
`Research/Quitting/StoppingLawMixtureFiniteWitnessPassport.lean`; it includes
`Never` and does not assert attainment of the cap.

A search of every current constructor/use of
`QuittingReprojectionConcentratedPacket` found no theorem composing an
arbitrary positive singleton stage atom, `FinFourMinimumAtomProducer`, or
owner-compressed singleton producer with this pure-time routing construction.
The result is therefore not a duplicate of the temporal tightness split or
the existing concentrated consumers.

Meaningful downstream obligations already consume this exact packet type in
`Research/Quitting/ConcentratedSingleton/Consumer.lean`,
`StrategicDispatch.lean`, `Cancellation.lean`, and
`Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`.  Those files
do not yet close every arm, which is why the corrected result closes the
*diffuse-minimum-singleton* question but not the concentrated-singleton
question.

## Required scope and nonclaims for export

The export should lead with the generic actual-data producer

\[
 \text{positive singleton stage atom + a distinct player}
 \Longrightarrow
 \text{actual recurrent concentrated packet},
\]

and state the atlas corollary

\[
 \text{every Fin4 weak concentrated-singleton origin}
 \Longrightarrow
 \text{actual recurrent concentrated packet}.
\]

It must explicitly state:

- every packet profile is a pure-time update of one literal source profile
  (the compressed endpoint in the minimum-owner-clock corollary);
- the original minimum source, chronology, and compressed endpoint remain
  retained as provenance in the adapter;
- the pure-time update generally changes the post-mark tail;
- the copied pre-anchor roots are literal roots, but their cap--Nash exactness
  is certified only over the original source suffix, not over the compressed
  or pure-time-updated target;
- no terminal witness is used;
- no target-side near-minimality, cap--Nash exactness, return, rank descent,
  terminal approximation, or uniform payoff is proved; and
- the remaining open node is consumption of the recurrent packet in
  `questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`.

Boundary checks are exact: the no-loss mass inequality can be equality when
the replaced observer already survives with probability one; `None` belongs
to the late mode; and the distinct-observer choice requires at least two
players (automatically true for `Fin 4`).  The theorem does not claim an
analogous one-player construction.

## Earlier conditional audit

The following audit explains why the original conditional proof is valid and
where its unnecessary premise entered.

## Verdict (superseded)

The packet-construction theorem is correct **conditional on** the displayed
input

\[
\Pr_{\tau_n}(\{j\}\text{ at }t_n)>\lambda,
\qquad d_j(\tau_n)\to0.
\]

It does produce every field of the existing
`QuittingReprojectionConcentratedPacket`, after the standard finite
subsequence choices.  The three routing modes lose no marked mass, and the
normalized moving-coordinate defect estimate is valid against unrestricted
behavioral deviations.

It does **not** close the weak minimum-singleton atlas leaf.  The checked
minimum-singleton producer supplies the fixed singleton mass and literal
source provenance, but not vanishing debt of the singleton owner.  Incentive-
aware compression scales/preserves that owner's source debt; it makes the
target debt vanish only when the source owner's debt already tends to zero.
An arbitrary positive minimum-law singleton owner may be active.

Accordingly the note's headline “consumes the weak owner-compressed minimum-
singleton endpoint” and its Scope claim are too strong.  The valid result is
an adapter for the **inactive-owner subclass**.  Since the resulting strong
packet still has unconsumed strategic arms, this is not an accepted output of
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md` and is not exportable as a
weak-to-strong atlas contraction.

Recommended disposition: **Research formalization / notes only**, with the
conditional premise and remaining active-owner branch explicit.

## Sources and exact API inspected

- `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`:
  `FinFourMinimumAtomChronology`,
  `FinFourOwnerCompressedSingletonEndpoint`,
  `FinFourOwnerCompressedSingletonProducer`, and
  `FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer`.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`:
  `QuittingReprojectionConcentratedPacket`,
  `tendsto_normalized_moving_coordinateNashDefect_zero`, and
  `positive_stageCoalitionMass_has_semanticPrefixIncidence` as used by the
  checked temporal split.
- `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean` and
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` for
  pure-time approximation of the unrestricted cap.
- `quittingContinuationBestResponseValue_update_self` for cap invariance under
  the observer's own strategy replacement.
- `quittingLiveMass_mul_coordinateNashDefect_le_initialDebt` for the full
  behavioral one-step Green bound.
- The concentrated-packet consumers in
  `Research/Quitting/ConcentratedSingleton/Consumer.lean`,
  `StrategicDispatch.lean`, and `Cancellation.lean`.

## 1. Near-cap response and debt

For each target `tau_n`, a terminal gap supplies some coordinate with debt at
least `gamma`.  Under the additional hypothesis `d_j(tau_n) -> 0`, this
coordinate differs from `j` eventually.  Finite pigeonhole fixes one observer
`o != j` on a subsequence.

For any `e_n > 0`, pure-time extremality supplies a complete deterministic
time `q_n in N union {infinity}` with payoff at least

\[
B_o(\tau_n)-e_n.
\]

Changing only `o` leaves its behavioral cap unchanged.  Hence for
`rho_n=tau_n[o <- Q_{q_n}]`,

\[
0\le d_o(\rho_n)\le e_n.
\]

This is a statement about the full behavioral cap, not a stationary or
one-stage surrogate.

Taking `s_n=1/(n+1)` and `e_n=s_n^2` is legitimate after reindexing the fixed
observer subsequence.

## 2. Exact three-mode mass routing

Let `E_n` be the source event `{j}` at `t_n`.  Independence of the complete
stopping laws gives the following literal comparisons.

1. If `q_n > t_n` or `q_n = infinity`, the replacement makes `o` Continue
   through `t_n`; deleting its old survival factor sends `E_n` into `{j}` at
   `t_n` with no mass loss.
2. If `q_n = t_n`, deleting the old `o`-survival factor sends `E_n` into
   `{j,o}` at `t_n`, again with no mass loss.
3. If `q_n < t_n`, the event defining `E_n` implies that every opponent of
   `o` survives through `q_n`; after forcing `o` to Quit there, it sends into
   `{o}` at `q_n` with no mass loss.

These are product-law inclusions.  Earlier absorption and Never atoms cause no
gap.  Passing to one of the three infinite mode classes fixes both the mode and
the nonempty terminal label.

## 3. Every concentrated-packet field is available

Work with the reindexed `rho` sequence and choose:

- `owner := o`;
- the fixed terminal from the selected routing mode;
- `mark n := t_n` in modes 1--2 and `mark n := q_n` in mode 3;
- `cutoff n := mark n + 1`;
- `scale n := 1/(n+1)`;
- `resolution := lambda`; and
- identity subsequence after reindexing.

The routed mass inequality gives `stageMass`.  It also gives positive root
coalition mass and the generic literal semantic-prefix identity required by
`semanticPrefix`.  Positivity of the scale and `mark_lt` are immediate.

The checked all-behavior Green inequality gives

\[
0\le
\frac{\operatorname{Live}_{\rho_n}(h_n)
      \operatorname{Defect}_o(\rho_n,h_n)}{s_n}
\le \frac{d_o(\rho_n)}{s_n}
\le s_n\to0,
\]

which is exactly `defect_tendsto`.  No post-date tail equality is a field of
`QuittingReprojectionConcentratedPacket`, so its loss under the complete
pure-time response is honestly outside this interface.

Thus there is no packet-API gap in the conditional theorem.

## 4. The missing entrance premise

`FinFourOwnerCompressedSingletonEndpoint` proves:

- actual singleton stage mass;
- unchanged opponents;
- unchanged owner cap;
- literal source prefix and post-date tail provenance; and
- source-side cap-stack exactness only.

It has no field asserting small owner debt.  The incentive-aware estimate has
the form

\[
d_j(\tau_n)\le C\,d_j(\sigma_n)
\]

for a fixed finite coefficient at a fixed resolution.  Therefore it yields
`d_j(tau_n) -> 0` only if `d_j(sigma_n) -> 0`.

The minimum joint-law source gives convergence of the source debt coordinate
to `d_j(point)`, not to zero.  Neither singleton law mass nor global minimum
provenance implies `d_j(point)=0`.  The current source type does not choose the
singleton owner outside `positiveDebtSupport`.

The two-player simultaneous-tie regression from the incentive-aware review
also shows that even an inactive owner does not prevent other coordinates from
becoming active after compression.  Hence minimum-fiber no-entry cannot be
used to manufacture the missing premise.

## 5. Conjecture-facing status

For a minimum-singleton source satisfying the additional inactive-owner
condition, this is a clean and useful source-to-strong-packet adapter.  In the
late-response mode its terminal `{j}` is distinct from packet owner `o`, which
does enter the strongest opponent-singleton branch of existing concentrated
machinery.  The other two modes enter the observer-containing collision and
observer-singleton branches.

Those branches are still not exhaustive semantic consumers of the strong
packet.  More importantly, the active-owner portion of the original weak leaf
never reaches the theorem.  Thus the map is

\[
\text{minimum singleton + inactive owner}
\longrightarrow
\text{strong concentrated packet},
\]

not

\[
\text{minimum singleton}
\longrightarrow
\text{strong concentrated packet}.
\]

This is not a strict contraction of the named weak node and should not replace
or remove it from the atlas.

## Required repair for export reconsideration

One needs an exhaustive producer for the missing active-owner case, for
example:

1. prove every minimum-law singleton source has an inactive selected owner;
2. consume the case `d_j(point)>0` directly; or
3. modify the near-cap routing so that an observer equal to `j`, including the
   late-response mode `q_n>t_n`, still yields a fixed positive reached atom and
   normalized packet defect.

Any repair must retain the actual minimum chronology rather than select an
independent strong packet.  Until then, the conditional theorem is rigorous
Research mathematics but not an export-gate result.
