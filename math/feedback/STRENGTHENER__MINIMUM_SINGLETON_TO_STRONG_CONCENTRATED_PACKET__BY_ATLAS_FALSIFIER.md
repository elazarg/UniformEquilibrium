# Adversarial review of minimum-singleton to strong concentrated packet

Reviewer: `ATLAS_FALSIFIER`

## Verdict

The routing and normalized-defect argument is mathematically sound.  The
note's original conditional version assumed that the singleton owner already
had vanishing debt.  That premise is **not** produced by the arbitrary
minimum-law singleton source: a positive singleton atom in the selected law
does not imply that its owner has zero semantic debt.

The current rewritten note makes the stronger and simpler repair which
removes this premise altogether.
Choose any fixed player `o != j`, replace `o` by an arbitrarily accurate
pure-time best response, and use `o` as the packet owner.  This creates the
needed vanishing full behavioral debt by construction, whether or not `o` was
profitable at the compressed source.  The same three routing cases preserve
the entire marked mass.  Thus the repaired theorem consumes the **whole**
minimum-singleton leaf into `QuittingReprojectionConcentratedPacket`; neither
the terminal exploitability witness nor an inactive singleton owner is needed
for this conversion.

Verdict on the current rewritten note: **PASS for mathematical export**, with
the explicit scope that it reaches the generic strong concentrated-packet
node and does not consume that node's remaining strategic leaves.

### Addendum: maximal static form

The later strengthening from a cofinal minimum-source family to one arbitrary
actual singleton row is also valid.  If its exact stage mass is `m>0`, repeat
that profile as the raw source sequence, use approximation errors tending to
zero, and run the same fixed-nonowner update.  The routing proof gives new
stage mass at least `m` in every retained mode, so the packet may take
`resolution=m` exactly.  Nothing in the packet definition requires the raw
profiles themselves to converge or the source ranks to increase.  This
generic form upgrades any supplied weak singleton core, not only the
minimum-law origin.

What it preserves is the weak core as external provenance and the updated
profiles' own literal current/root/tail edges.  It does not preserve literal
equality with the weak core's old post-date tail, and the export states this
loss explicitly.  There is no mathematical objection to the exact constant
or the static specialization.

### Addendum: local best-endpoint exactification

There is a strictly simpler maximal form which should replace the pure-time
construction in the final export.  At the displayed singleton row choose any
`o != j` and let

\[
 a=\texttt{quittingRootBestEndpointAction}(r,u^+,x,o),
\]

where `x` is the actual live root at the marked date and `u^+` is the
prescribed payoff of the literal spine strictly after that date.  Change only
`o`'s action at that one date to `PMF.pure a`.

This exactification is aligned with the packet defect, not merely with an
auxiliary tail:

- `quittingProfileLiveRoot_literalOneDateProfile_tail_eq` preserves every
  post-date root and hence the prescribed tail semantic pair;
- every opponent marginal at the marked root is unchanged;
- `quittingRootEndpointDifference_update_self` says that changing `o`'s own
  root marginal does not change its Quit-versus-Continue comparison; and
- a pure action selected by `quittingRootBestEndpointAction` has coordinate
  Nash defect exactly zero (ties are resolved toward Continue and are also
  harmless).

The routing now has only two cases.  If `a=false`, the old `{j}` atom routes
to `{j}`; if `a=true`, it routes to `{j,o}`.  Since `o` was outside the old
singleton, both routed coalitions are nonempty and removing its old action
factor cannot reduce mass.  The live mass before the row and the complete
tail after it are literally unchanged.

Repeat this single updated profile, keep the marked date and cutoff constant,
use the identity subsequence, and take any positive scale tending to zero.
The normalized defect is identically zero.  Hence this local theorem gives a
packet of exact resolution equal to the source stage mass while preserving
the old literal post-date tail.  It requires neither pure-time extremality,
an approximate cap selector, the Green inequality, a mode subsequence, nor a
cofinal source sequence.

Adversarial verdict on this final simpler theorem: **PASS**.  Its exact
orientation uses the same prescribed tail and the same coordinate defect as
the packet.

One declaration-level correction was required in an intermediate export that
claimed literal equality of the complete behavioral strategy after the row.
`quittingStagePureEndpointBehaviorDeviation` resumes the same canonical
**live-root word**, but it need not equal the source strategy on irrelevant
off-live histories.  Define the target with
`quittingLiteralOneDateProfile` from
`Research/Quitting/SameStageEndpointMonodromy.lean` to obtain the claimed
literal full-strategy tail, or weaken the prose to equality of post-date live
roots.  The packet itself only needs the latter.  The final export now uses
the literal one-date constructor and its checked root, live-mass, and tail
identities, so it supports the stronger wording.  This was an
interface/provenance wording repair, not a mathematical obstruction.

### Addendum: arbitrary nonempty stage coalition

The final extension from a singleton `{j}` to an arbitrary nonempty source
coalition `A` is valid under the single exclusion `A != {o}`.  The four
membership/action cases for the routed coalition are

\[
\begin{array}{c|c|c}
o\in A&a=C&A\setminus\{o\},\\
o\in A&a=Q&A,\\
o\notin A&a=C&A,\\
o\notin A&a=Q&A\cup\{o\}.
\end{array}
\]

Pure-endpoint routing removes the old `o`-factor and therefore does not lower
root mass in any case.  The only potentially empty output is the first row,
and it is empty exactly when the nonempty source coalition is `{o}`.  Thus
`A != {o}` is both the precise boundary needed for the uniform statement and
strictly weaker than requiring `o` to lie outside `A` or requiring `A` to be
nonsingleton.  If `A={o}` and Quit is selected, the construction still works;
if Continue is selected, the row routes to the empty coalition and the
displayed atom cannot populate the packet's nonempty-terminal field.

The literal-one-date version now used in the export fixes the earlier
provenance wording issue.  The exact-zero defect proof is unchanged because
the best endpoint is computed from the same prescribed post-row payoff used
by the packet, and own-marginal replacement leaves both endpoint values
unchanged.

Verdict on the maximal arbitrary-`A` theorem: **PASS**.

## Declarations inspected

- `FinFourOwnerCompressedSingletonEndpoint` and
  `FinFourMinimumAtomChronology.nonempty_ownerCompressedSingleton` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `QuittingReprojectionConcentratedPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`;
- `quittingLiveMass_mul_coordinateNashDefect_le_initialDebt` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionWindow.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
- `quittingContinuationBestResponseValue_update_self` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTightness.lean`.

## 1. Why the original owner-debt input had to be removed

The exact owner-compressed endpoint contains:

- a literal reference profile and one-date target profile;
- a selected stage after the retained source root word;
- a fixed strict singleton stage-mass floor;
- literal equality of every unmodified root and of the post-date tail; and
- preservation of the owner's cap under its one-date update.

It contains no target-side Nash or debt estimate.  In fact the module's own
documentation explicitly says that no target-side Nash, near-minimum,
low-tail, return, or regeneration statement is asserted.  The exact cap-Nash
stack remains certified only above the unmodified suffix.

The incentive-aware compression estimate bounds target owner debt by a
multiple of source owner debt.  It makes that target debt vanish only if the
singleton owner is inactive at the limiting minimum semantic pair.  Neither
`FinFourMinimumAtomProducer` nor the causal singleton-law atom says this.  A
terminal-law statement and an owner cap/payoff statement are different data.

Accordingly, the original conditional proof was valid on its stated subcase,
but its premise could not close the arbitrary `minimumSingleton` atlas leaf.
The rewritten theorem no longer uses it.

This is a source-interface gap rather than a counterexample under all the
positive-minimum hypotheses.  Constructing the latter would amount to a
quitting-game counterexample.  The elementary profile where `j` quits alone
for payoff `-1` and prefers Never shows why the law atom alone has no local
implication for `d_j`; it does not satisfy the positive-global-minimum
premise and is cited only as a separation of the two kinds of datum.

## 2. The profitable-observer step is unnecessary

Fix once and for all any `o != j`; this is available on `Fin 4`.  For every
compressed endpoint `tau_n`, let

\[
 s_n=\frac1{n+1},\qquad e_n=s_n^2>0.
\]

Pure-time extremality and the elementary approximation property of a
supremum give `q_n : Option Nat` such that

\[
 U_o(\tau_n[o\leftarrow Q_{q_n}])
 \ge B_o(\tau_n)-e_n.
\]

Set `rho_n = tau_n[o <- Q_{q_n}]`.  A player's cap depends only on its
opponents.  The checked update-self identity therefore gives

\[
 B_o(\rho_n)=B_o(\tau_n),
 \qquad 0\le d_o(\rho_n)\le e_n.
\tag{1}
\]

No lower bound on `d_o(tau_n)` is used.  In particular, `o` need not be a
profitable observer and the terminal witness is irrelevant to this step.

This removes both delicate uses of the original premise:

1. there is no need to infer that a full-gap player is distinct from `j`;
2. there is no need to prove `d_j(tau_n) -> 0`.

## 3. Adversarial check of all routing modes

Let `E_n` be the original event that the terminal coalition is `{j}` at
date `t_n`.  On this event

\[
 T_j=t_n,qquad T_k>t_n\quad(k\ne j).
\]

Only `o` is replaced.  Removing its old survival factor cannot decrease the
probability of the event involving the remaining clocks.

- If `q_n > t_n` or `q_n = infinity`, the remaining event terminates as
  `{j}` at `t_n`.
- If `q_n = t_n`, it terminates as `{j,o}` at `t_n`.
- If `q_n < t_n`, the remaining event implies that every opponent of `o`
  survives through `q_n`; it therefore terminates as `{o}` at `q_n`.

In every case the new stage mass is at least `Pr(E_n)`, not merely a fixed
fraction of it.  The `q_n < t_n` case is sometimes easy to misstate: one must
delete `o`'s old marginal first and weaken all other players' survival from
`> t_n` to `> q_n`.  Both operations increase the relevant product mass.

The modes form a finite partition.  An infinite subsequence fixes one mode,
and hence fixes the marked terminal subtype and the formula for the marked
date.  If desired, `q>t` and `Never` can be one mode because they have the
same marked date and coalition.

No behavioral-strategy legality problem occurs.  A quitting game has one live
history at each date, and `quittingPureTimeBehaviorStrategy` is an actual
behavior strategy.  The stage-mass comparison is a product-law identity, not
a coupling of dependent clocks.

## 4. Normalized defect and exact packet fields

For the updated actual profile, the checked Green estimate gives

\[
 \operatorname{Live}_{\rho_n}(h_n)
 \operatorname{Defect}_o(\rho_n,h_n)
 \le d_o(\rho_n)\le e_n=s_n^2.
\]

Since `s_n>0` and `s_n -> 0`, division by `s_n` yields the required limit.
This is exactly the expression in the `defect_tendsto` field of
`QuittingReprojectionConcentratedPacket`; it is not a stationary or
one-stage substitute for behavioral debt.

The remaining fields match as follows.

- Use the routed profiles as `profiles`.
- Use `cutoff_n=h_n+1`, so `mark_lt` is immediate.
- Use the fixed positive lower bound `lambda` as `resolution`; the strict
  source bound gives the packet's weak inequality.
- A positive stage mass implies positive live mass and positive root
  coalition mass.
- The current/tail carrier membership and exact semantic prefix identity are
  the generic spine decomposition of the same literal routed profile.
- Retain a strict mode subsequence, or reindex that subsequence and use the
  identity map.  The scale limit is preserved along a strict subsequence.

The packet does **not** require the old cap-Nash stack, near-minimum debt, the
old post-date tail, or a payoff gain from `tau_n` to `rho_n`.  None should be
silently added to the output.

## 5. Exact scope of the repaired contraction

For every positive `lambda` below the selected singleton-law mass and every
requested causal depth, the checked owner-compression theorem supplies a
literal endpoint beyond that depth.  Choosing such endpoints cofinally and
performing the arbitrary-nonowner near-cap update above produces the strong
concentrated packet.

This answers the first acceptable output in
`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`: actual marked dates,
a fixed positive stage-mass floor, and literal semantic source/tail
provenance at the marked row.  It does not assert that the updated row retains
the old source's cap-Nash provenance.  The exactness is instead the packet's
own current/root/tail identity.

It also does not consume `QuittingReprojectionConcentratedPacket` into a
uniform equilibrium or rank decrease.  The concentrated packet's documented
strategic leaves remain downstream.  The mathematical advance is the removal
of the diffuse minimum-singleton atlas leaf, not a proof of Fin4.

## Unresolved objections

None.  The rewritten note no longer suggests that vanishing singleton-owner
debt is supplied by arbitrary minimum-law compression, and it explicitly
distinguishes the updated profile's literal semantic prefix from the old
source's cap-Nash stack.
