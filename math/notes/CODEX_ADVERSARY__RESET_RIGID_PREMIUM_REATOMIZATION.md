# Reset-rigid global minima can be re-atomized, but the reset itself is horizontal

**Author:** `CODEX_ADVERSARY`  
**Status:** proved ordinary mathematics from the named checked declarations;
two source-refinement wrappers and one finite same-date premium-transport
theorem are proposed.  This is not a uniform-equilibrium consumer and is not
an export candidate.  
**Date:** 2026-08-31

## 1. Question and disposition

Consider the reset-rigid arm produced inside the actual `Fin 4`
no-uniform-payoff argument.  Its returned joint point is

\[
 z=((u,c),\mu),\qquad D(z)=D_*>0,
\]

and the reset owner `o` satisfies `d_o(z)=c_o-u_o=0`.  The point lies on the
global minimum fibre, not merely on a minimum face of an arbitrary hull.

There are two conclusions.

1. The reset dispatch's debt-transfer inequality has **no slack at all** at
   this source.  It is an algebraic equality forced by equality of the two
   total debts.  Consequently it cannot orient a recipient or lower a debt-
   support rank.
2. The global singleton moat does give a useful replacement for the stalled
   reset: it selects either a quantitative Never premium or a finite atom in
   the *retained law* carrying a quantitative owner surplus.  In the finite
   branch that exact atom can be causalized at the returned point and made the
   chosen atom of a fresh `FinFourMinimumAtomProducer`.  In the singleton
   subbranch the reset owner can additionally be prescribed as the packet
   owner, giving an exact owner-aligned singleton-versus-pair action split on
   one common chronology.

This is a genuine source refinement, but not a descent: the new producer is
still at the same semantic minimum and the existing contracted consumer still
ends in its strategic or collision-minimum residual.  Exact regressions below
show that the quantitative moat, retained atom, strict toggle, literal causal
row, and unique all-Continue cap root do not themselves orient the chamber.

## 2. Exact global-fibre geometry

Write

\[
 d_i=c_i-u_i,\qquad D_*=\sum_i d_i.
\]

At every returned minimum-fibre point, checked carrier nonnegativity and the
global singleton margin give

\[
 d_i\ge 0,
 \qquad c_i-r_i(\{i\})\ge D_*\quad(i\in I).       \tag{2.1}
\]

The complete law fixes `u` by
`terminalSemanticLawCarrier_rewardMoment`.  Hence the entire fixed-law
global-minimum fibre embeds in the compact cap simplex

\[
 c_i\ge r_i(\{i\})+D_*,
 \qquad \sum_i c_i=\sum_i u_i+D_*.                 \tag{2.2}
\]

This geometry is horizontal.  Let `x` be the global-minimum source used by a
reset dispatch and let `y` be its returned point.  Suppose

\[
 D(x)=D(y)=D_*,\qquad d_o(y)=0.
\]

Then, without using any law information,

\[
\begin{aligned}
 \sum_{j\ne o}\bigl(d_j(y)-d_j(x)\bigr)
 &=D(y)-D(x)-\bigl(d_o(y)-d_o(x)\bigr)\\
 &=d_o(x).                                          \tag{2.3}
\end{aligned}
\]

Thus `QuittingFixedLawResetDispatch.transfer`, which states the weak
inequality from the right side of (2.3) to the left side, is automatically an
equality on the actual global fibre.  It carries no strictness.  It also does
not preserve old zero coordinates: the vectors

\[
 (a,0,0,0)\longmapsto(0,a/3,a/3,a/3)
\]

already obey every debt-side equality in (2.3) while reducing, rather than
increasing, the number of zero coordinates.  Some additional cap/profile
field would be needed to exclude this redistribution.

## 3. The retained-law quantitative alternative

Put `s_o=r_o({o})`.  Since `d_o(z)=0`, (2.1) says

\[
 u_o-s_o=c_o-s_o\ge D_*.                           \tag{3.1}
\]

The law moment identity turns this into

\[
 D_*\le \mu(\mathsf{Never})(-s_o)
       +\sum_{\varnothing\ne S\subseteq I}
          \mu(S)\bigl(r_o(S)-s_o\bigr).             \tag{3.2}
\]

For `Fin 4`, (3.2) gives the exhaustive quantitative split

\[
 \boxed{
 \mu(\mathsf{Never})(-s_o)\ge D_*/2
 \quad\text{or}\quad
 \exists S\ne\{o\}:\
 \mu(S)\bigl(r_o(S)-s_o\bigr)\ge D_*/30.}           \tag{3.3}
\]

Indeed, if the Never term is below `D_*/2`, the sum of the fifteen finite
terms is above `D_*/2`, so one is at least `D_*/30`.  The selected finite
term is positive and cannot be the owner's singleton.  The terminal
exploitability witness gives a strict membership toggle on this same `S`.

If `|r_i(T)|<=M`, then `D_*>0` implies `M>0`, and the finite branch further
gives

\[
 \mu(S)\ge \frac{D_*}{60M},\qquad
 r_o(S)-s_o\ge \frac{D_*}{30}.                      \tag{3.4}
\]

The second inequality uses `mu(S)<=1`; the first uses
`r_o(S)-s_o<=2M`.  In the Never branch,

\[
 \mu(\mathsf{Never})>0,\qquad s_o<0,qquad
 \mu(\mathsf{Never})\ge \frac{D_*}{2M}.             \tag{3.5}
\]

The nonquantitative sharpening in
`CODEX_ROOT__RESET_RIGID_GLOBAL_MOAT_ALIGNED_LAW_SURPLUS.md` is also valid:
if the support outcome selected directly from the average in (3.2) is Never,
then `s_o<=-D_*`; otherwise that selected finite atom has pointwise owner
surplus at least `D_*`.

## 4. New source refinement: re-atomize at the returned point

### Proposition 4.1 (premium re-atomization)

Assume the actual `Fin 4` hard-residual data are retained together with the
reset chamber, and let `z` be its returned joint point.  In the finite arm of
(3.3), there is a `FinFourMinimumAtomProducer` whose

- point is exactly `z`;
- residual is the same table-level hard residual;
- chosen terminal is exactly the atom `S` from (3.3); and
- atom therefore retains both the product floor in (3.3) and the same strict
  terminal toggle.

Consequently the checked
`FinFourMinimumAtomProducer.nonempty_contractedConsumer` applies with this
premium-aligned atom, rather than with the independently selected atom used
to enter the chamber.

### Proof

The proof of
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` starts from an
origin whose debt is the positive literal infimum.  The selected hull minimum
has debt at most the origin debt and, as a carrier point, at least the same
global infimum.  Hence its debt equals the infimum.  Every returned point in
the minimum face has the same debt and is therefore also a global minimum.
The chamber field `dispatch.joint` supplies joint-carrier membership of `z`.

Apply
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` to `z`,
the exact finite atom `S`, its positive law mass, the positive debt infimum,
and the just-proved debt equality.  Package its conclusion as a
`QuittingMinimumLawCausalSuffixAtom` with terminal `S`.  Together with the
hard residual, joint and semantic carrier membership, global minimality, and
debt equality, these are exactly the fields of `FinFourMinimumAtomProducer`.
The contracted-consumer declaration is then applicable verbatim. `QED`

This is an actual renewable source operation: it retains the table residual,
global minimum, exact law atom, and arbitrarily deep source-matched cap words.
It is not a chronological edge from the old semantic point to the new one;
the point has not moved.

### Never arm

The same construction still gives a producer in the Never arm.  Use the
positive finite atom already present in
`QuittingFixedLawResetDispatch.supported_toggle`; it contains the displayed
`other != owner`, so it is not `{owner}`.  What is additionally retained is
the quantitative Never certificate (3.3) or the pointwise negative-singleton
certificate described after (3.5).  There is presently no checked consumer
of this combined finite-atom/positive-Never passport.

## 5. Stronger singleton role alignment

Suppose the finite premium atom is a singleton, `S={j}`.  Then `j!=o`.
The generic contracted producer is stronger than necessary but chooses a
distinct packet owner abstractly.  Here the reset owner can be prescribed.

### Proposition 5.1 (owner-aligned singleton clock)

Let `mu=mu({j})` and put `lambda=mu/2`.  On one fixed chronology of the
premium re-atomized source, beyond every requested depth there is an actual
owner-compressed singleton row of mass greater than `lambda`.  Updating the
reset owner `o` at that row to its exact best Boolean endpoint produces a
`FinFourSingletonStageStrongConcentratedPacket` with

\[
 \texttt{singletonOwner}=j,\qquad
 \texttt{packetOwner}=o.                             \tag{5.1}
\]

Its checked action-indexed consumer has exactly the following form.

- In Continue mode the routed terminal remains `{j}` and the concentrated
  singleton strategic arm holds.
- In Quit mode the routed terminal is exactly `{o,j}` and a
  `QuittingConcentratedCollisionMinimumResidual` is produced with owner `o`.

Moreover the selected scale is linearly aligned with the premium:

\[
 \lambda\bigl(r_o(\{j\})-s_o\bigr)\ge D_*/60.       \tag{5.2}
\]

### Proof

Use
`exists_commonChronology_cofinal_ownerCompressedSingleton` with
`lambda=mu/2`.  Its endpoint has a literal stage singleton mass greater than
`lambda`.  The proof of
`FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
uses only a player distinct from the singleton owner.  Instead of its
arbitrary finite choice, insert the already supplied `o`, using `o!=j`, and
apply `QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass`.
The strong-packet structure is then filled with (5.1).  The two routed labels
follow directly from `routedTerminal_mode_and_card`, and the consumer from
`actionIndexedConsumerResult`.  Finally (5.2) is half of the product floor in
(3.3). `QED`

This is the strongest genuine orientation I found.  It turns the reset owner
into a causal packet role and, in Quit mode, fixes the exact transverse pair.
It still does not choose the Boolean mode, force the shifted tail back to the
minimum, or consume either returned arm.

## 6. Exact local regressions

### 6.1 Checked collision regression

The checked namespace `QuittingResetIncidenceCapRegression` gives a literal
two-player profile with

\[
 \mu=\delta_{\{0,1\}},\quad u=(1,0),\quad c=(1,1),
 \quad d=(0,1),\quad D=1.                             \tag{6.1}
\]

Take owner `o=0`.  Its singleton reward is `-1`, the other singleton reward
is `0`, and the owner's collision reward is `1`.  Therefore

\[
 c_0-r_0(\{0\})=2\ge D,qquad
 c_1-r_1(\{1\})=1=D,                                 \tag{6.2}
\]

while the retained collision has owner surplus `2`, mass one, and a strict
leave toggle.  The atom occurs at a literal stage with mass one.  Nevertheless
`exact_capNash_forces_allContinue` proves that every exact root against `c`
is all Continue.

Taking source, target, and returned pair all equal to (6.1) satisfies the
local `QuittingFixedLawResetDispatch` fields: both debt comparisons and the
transfer are equalities, the supported toggle is the displayed leave edge,
and the dynamic arm is the all-Continue fixed point.  Thus even the numerical
global moat at every coordinate, the aligned quantitative atom, literal
chronology, and full local reset structure do not produce an absorbing cap
root or a rank direction.

This is not a global positive minimum.  Against all-Never opponents the
all-Continue profile has payoff and behavioral cap zero, so the global debt
infimum is zero and the game has an immediate uniform equilibrium.  That is
exactly the missing hypothesis which the regression isolates.

### 6.2 Singleton hidden-clock regression

There is an equally elementary singleton version (ordinary mathematics, not
a named Lean declaration).  Let the players be `o,j` and define

\[
\begin{array}{c|ccc}
 &\{o\}&\{j\}&\{o,j\}\\ \hline
 r_o&0&2&0\\
 r_j&0&-1&1
\end{array}                                           \tag{6.3}
\]

In the displayed profile, `j` Quits at date zero and `o`, on the unreachable
continuation, Quits at date one.  Then

\[
 \mu=\delta_{\{j\}},\quad u=(2,-1),\quad c=(2,1),
 \quad d=(0,2),\quad D=2.                             \tag{6.4}
\]

The cap calculation is unrestricted: `o` gets `2` by continuing at date zero;
`j`, after deviating to Continue at date zero, gets `1` by joining `o` at
date one.  Thus both moat inequalities are equalities, and the retained
singleton has owner surplus `2=D`.

If `x` is `o`'s root Quit probability, the endpoint differences against `c`
are

\[
 \Delta_o=-2,qquad \Delta_j=3x-2.                   \tag{6.5}
\]

Exact complementarity first forces `x=0` and then forces `j` to Continue, so
all Continue is again the unique exact cap root.  Every pure terminal
coalition has a unit strict toggle: `j` joins `{o}`, `j` leaves `{j}`, and `o`
leaves `{o,j}`.  The atom and the hidden downstream cap clock belong to one
literal profile.

Again the global infimum is zero: against all-Never opponents, `o` can obtain
only zero by quitting and `j` weakly prefers Never to its negative singleton.
This example is not punishment-normal at `j`.  Its exact force is narrower:
a premium singleton, zero owner debt, a downstream cap clock, all numerical
moat inequalities, and the terminal-toggle witness do not decide the
owner-aligned packet's action or yield an absorbing cap root.

## 7. Precise residual

After using every field above, the reset-rigid chamber reduces to the
following two typed source passports.

1. **Never-premium source:** a global minimum-atom producer at the returned
   point, a finite atom distinct from the reset owner, and
   `mu(Never)(-s_o)>=D_*/2` (or the pointwise `s_o<=-D_*` support
   certificate).
2. **Finite-premium source:** a global minimum-atom producer whose chosen
   atom `S!= {o}` satisfies the product floor `D_*/30` and the hard strict
   toggle.  If `S` is a singleton, the reset owner is the packet owner and
   the only remaining local modes are the exact singleton strategic arm and
   the exact pair collision-minimum residual.

Neither passport includes a return, a law-changing monotone rank, a
punishment-floor exact Bellman edge, or a selector forcing the packet action.
The reset transfer itself cannot supply one because of (2.3).  Any further
claim based only on the pointwise moat and local reset fields is excluded by
Section 6.  A real completion must use global minimality on the *targets of a
new executable deviation* (hence force compensating cap leakage) and then
control that leakage chronologically.

## 8. Declarations and files inspected

- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
- `terminalSemanticLawCarrier_rewardMoment` in
  `TerminalSemanticMinimumAggregateSurplusConsumer.lean`;
- `QuittingFixedLawResetDispatch`,
  `exists_fixedLawResetDispatch`, and the checked
  `QuittingResetIncidenceCapRegression` namespace in
  `TerminalSemanticResetIncidenceCapReturn.lean`;
- `QuittingLawTightResetRigidChamber` and
  `exists_quittingLawTightResetRigidChamber` in
  `LawTightCapNashStrictMinimum.lean`;
- `finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` in
  `FinFourLawTightCapNashStrictMinimum.lean`;
- `QuittingMinimumLawCausalSuffixAtom` and
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
  `TerminalSemanticLawCarrierCausalization.lean`;
- `exists_resetFaceLaw_concentratedPacket_of_collision` in
  `TerminalSemanticResetFaceLawTemporalSplit.lean` and
  `QuittingReprojectionDiffuseWindowPacket.terminal_card_eq_one` in
  `TerminalSemanticNonsingletonAntiDiffusion.lean`;
- `FinFourMinimumAtomProducer` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`;
- `exists_commonChronology_cofinal_ownerCompressedSingleton` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `FinFourSingletonStageStrongConcentratedPacket`,
  `routedTerminal_mode_and_card`, and
  `nonempty_of_singleton_stageMass` in
  `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`;
- `FinFourMinimumAtomProducer.nonempty_contractedConsumer` and
  `FinFourSingletonStageStrongConcentratedPacket.actionIndexedConsumerResult`
  in the Fin4 producer-atlas contraction modules; and
- `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` in
  `TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`.

The last declaration independently explains the concentrated minimum-tail
branch: positive absorption near the compact minimum fibre has a uniform
total-defect price.  It does not orient which non-owner coordinate pays that
price and therefore does not strengthen (2.3) into a rank.

## 9. Executable finite-premium selector

The role-aligned singleton construction in Section 5 uses the actual mixed
row.  There the reset owner's exact best endpoint need not preserve the
premium carried by one atom: endpoint optimality is an average over all
opponent actions.  Pureifying the marked row first removes precisely this
cancellation.  This does not preserve near-minimality, but it does preserve
the complete post-date source spine and gives a useful exact finite chain.

### Proposition 9.1 (premium-preserving pure-row endpoint)

Let `S != {o}` be the finite atom from the pointwise retained-law alternative,
so

\[
 r_o(S)-s_o\ge D_* .                                \tag{9.1}
\]

Suppose one of its causal source profiles has a marked date `t` with
unconditional `S`-mass at least `lambda>0`.  Replace the entire live root at
`t` by the pure coalition `S`, leaving every other date and every off-date
behavior rule unchanged.  Then replace only `o`'s marginal at `t` by its exact
best Boolean endpoint.  Let `T` be the resulting pure terminal coalition.
Then

\[
 T\ne\varnothing,\qquad T\ne\{o\},\qquad
 r_o(T)\ge r_o(S)\ge s_o+D_*,                        \tag{9.2}
\]

the `T`-mass at `t` is the complete live mass `L>=lambda`, the shifted
post-date spine is unchanged, and `o` has zero marked local Nash defect.

### Proof

At the pure `S` row, both endpoint actions of `o` absorb immediately.  This
is clear when `o` is absent from `S`; when `o` belongs to `S`, the Continue
endpoint still leaves the nonempty coalition `S.erase o`, because
`S != {o}`.  The endpoint comparison is therefore exactly between

\[
 r_o(S\mathbin{\setminus}\{o\})
 \quad\hbox{and}\quad
 r_o(S\cup\{o\}),                                   \tag{9.3}
\]

with the evident redundant endpoint when membership already agrees.  The
original `S` reward is one of these two values, so the selected maximum gives
(9.2).  Both routed coalitions contain a player different from `o`.
Pureification puts all reached mass `L` on `S`, and the endpoint adapter
routes all of that mass to `T`.  Its standard target-tail and
`ownerMarkedDefect_eq_zero` identities give the remaining claims. `QED`

This is an exact action selector, but on a literal pure sibling of the source
row rather than on the original mixed row.  That distinction is essential.

## 10. A same-date premium-or-transfer chain

The selector can be combined with global minimality more strongly than the
generic collision half-dichotomy because its selected root is pure.

### Proposition 10.1 (Fin4 premium transport or bilateral transfer)

Under Proposition 9.1 and the actual punishment-normal `Fin 4` hard residual,
there is a chain of at most three pure-coordinate updates at the same marked
date, all with the same post-date source spine and the same live mass
`L>=lambda`, having the following properties.

1. The first target is the pure coalition `T` of Proposition 9.1 and carries
   owner premium at least `D_*`.
2. A later edge is a literal best-endpoint update whose mover gain `G`
   satisfies
   \[
      G\ge \lambda D_*/3.                            \tag{10.1}
   \]
   The mover's unrestricted behavioral debt drops by exactly `G`, and the
   complete marked mass is routed without loss.
3. Either the final routed coalition `U` still satisfies
   \[
      r_o(U)-s_o\ge D_*/2,                            \tag{10.2}
   \]
   or one intervening edge is made by a player `a != o` and simultaneously
   gives
   \[
   \begin{aligned}
      &u_a(\hbox{after})-u_a(\hbox{before})
          \ge \lambda\min\{\gamma,D_*/3\},\\
      &u_o(\hbox{before})-u_o(\hbox{after})
          > \lambda D_*/4.                           \tag{10.3}
   \end{aligned}
   \]
   where `gamma` is the retained terminal exploitability gap.  Thus failure
   to transport half the premium exposes one reached, same-history,
   quantitatively paid cross-player loss edge.  If `T` is already
   nonsingleton, the sharper owner-loss lower bound is `lambda*D_*/2`.

### Proof

First suppose `|T|>=2`.  At the pure `T` row the exact pure-nonsingleton debt
identity gives

\[
 D(X_t)=\sum_i \delta_i,                              \tag{10.4}
\]

where `X_t` is the semantic current point and `delta_i` is player `i`'s local
root defect.  Global minimality gives `D(X_t)>=D_*`, while Proposition 9.1
gives `delta_o=0`.  One of the other three players, say `p`, therefore has
`delta_p>=D_*/3`.  Its exact endpoint update has gain
`G=L delta_p>=lambda D_*/3`, exact self-debt subtraction, unchanged shifted
tail, and no loss of the pure routed mass.

Let `U` be its routed coalition.  If (10.2) fails, then (9.2) gives

\[
 r_o(T)-r_o(U)>D_*/2.                                \tag{10.5}
\]

Here `p != o`; hence this is an actual loss of more than `lambda D_*/2` in
`o`'s complete payoff, while the mover gains at least `lambda D_*/3`.

Now suppose `T={j}`.  Punishment normality plus the terminal gap supplies the
checked collider `k != j` with

\[
 r_k(\{j,k\})-r_k(\{j\})\ge\gamma.                   \tag{10.6}
\]

At the pure singleton row its exact endpoint is therefore Quit, producing
the pure pair `V={j,k}` with mover gain at least `lambda gamma` and zero
`k`-defect.  Apply (10.4) to this pair.  One of the other three coordinates
has defect at least `D_*/3`, giving the later paid endpoint (10.1).

Track `o`'s terminal reward across the collider edge and the final paid edge.
If the final reward is at least `s_o+D_*/2`, (10.2) holds.  Otherwise, since
the starting reward at `T` is at least `s_o+D_*`, the total loss across the
two edges exceeds `D_*/2`; hence one edge loses more than `D_*/4` in terminal
reward and more than `lambda*D_*/4` in the complete payoff.  An edge made by `o` cannot
decrease `o`'s payoff because it is its own exact best-endpoint update, so the
losing edge has a non-owner mover.  The collider edge pays at least
`lambda gamma`; the final edge pays at least `lambda D_*/3`.  Thus its mover
gain is at least `lambda*min(gamma,D_*/3)`.  This proves (10.1)--(10.3).
`QED`

## 11. What the new chain does and does not consume

The finite-premium action mode is no longer unselected after passing to the
pure sibling: the reset owner first chooses a premium-preserving adjacent
face, and global minimality then forces a paid endpoint after at most one
punishment-normal singleton-to-pair bridge.  This is a source-attached
same-date sibling construction: all profiles share the original post-date
spine and the original chronological ancestry up to the marked row.  The
initial pureification changes several players simultaneously and is **not**
a unilateral deviation or a forward transition of the original chronology;
only the subsequent endpoint edges are literal unilateral updates.

It still is not a renewable edge.  Pureification can raise total semantic
debt by a fixed amount, so the paid target need not be near the global
minimum.  Neither the retained premium nor the cross-player loss is forced
to survive the final endpoint.  Consequently the existing near-minimum
opponent-transfer and capacity-slice consumers cannot be applied to the
chain without an additional return or an a priori bound on the pureification
excess.

The loss of premium at a paid endpoint is a real independent degree of
freedom.  At a pure row `T={1,2}`, take a distinct mover `p=3` and observer
`o=0`, set

\[
 r_o(T)=1,\quad r_o(T\cup\{p\})=-1,
 \qquad r_p(T)=0,\quad r_p(T\cup\{p\})=1.             \tag{11.1}
\]

The `p` endpoint is strictly paid while it destroys the entire observer
premium.  Replacing the first `-1` by `1` preserves the paid mover data and
instead preserves the premium.  This is an exact one-row regression, not a
full positive-minimum counterexample; it proves that no local endpoint
identity can choose between the two arms of Proposition 10.1.

## 12. Additional declarations inspected

- `QuittingStageAtomConcentratedPacketAdapter`,
  `sourceStageMass_le_targetStageMass`, `targetTail_eq_sourceTail`,
  `sourceToTargetGain_eq_liveMass_mul_defect`, and
  `ownerMarkedDefect_eq_zero` in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
- `quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect` as used
  in `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean`;
- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  in `PunishmentNormalAtomicCollisionHandoff.lean`;
- `FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket` and
  its source-preserving counterpart in the Fin4 producer atlas; and
- `quittingStageBestEndpoint_nearMinimum_opponentTransfer` in
  `TerminalSemanticLiveWeightedCollisionTransfer.lean`.
