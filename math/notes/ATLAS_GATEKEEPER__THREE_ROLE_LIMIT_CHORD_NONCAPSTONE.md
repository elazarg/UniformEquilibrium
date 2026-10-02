# The three-role limit chord is not a standalone capstone

Author: `ATLAS_GATEKEEPER`

## Status

The exact `ThreeRoleLimitChord` fields, even after restoring the common
actual source/one-player-replacement sequence used to construct them, do not
force support descent, a charged return, or quantitative total-debt ascent.

There is one useful exact strengthening in the minimum-target arm: the whole
debt vector is affine on the common stopping-law chord, so every proper
interior point has support equal to the union of the endpoint supports.  That
gives support growth when the target opens a new coordinate, and support loss
when no coordinate opens and the mover is actually killed.  The checked
`ThreeRoleLimitChord` supplies neither exclusion: its mover debt only drops by
a fixed amount and may remain positive, while another coordinate may enter.

The finite tableau below is an exact countermodel to every argument using
only nonnegative semantic debts, global minimum on the displayed carrier,
common-chord affinity, own-cap invariance under unilateral replacement, and
the stated mover/recipient floors.  It is deliberately not asserted to be a
quitting-game carrier: realizing it as the full carrier with positive global
minimum would itself refute the conjecture.  Its purpose is sharper—it proves
that the existing chord interface and its discarded actualization data do not
contain a well-founded orientation.  Any successful consumer must use an
additional quitting-specific chronological or source-regeneration fact.

## 1. Exact checked input

In
`Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`, the structure

```text
ConcentratedCollisionFourRole.ThreeRoleLimitChord
```

stores carrier points `sourceLimit` and `targetLimit`, distinct roles, and,
writing

\[
 D_* = D(\text{minimum}),\qquad
 a=\frac{\lambda^2D_*}{2n},\qquad
 b=\frac{\lambda^2D_*}{4n^2},
\]

the inequalities

\[
 D(X)=D_*,\qquad D(Y)\ge D_*,
\tag{1}
\]

\[
 d_m(Y)\le d_m(X)-a,
 \qquad
 d_r(Y)-d_r(X)\ge b,
\tag{2}
\]

with `m != owner` and `r != m`, followed by the tautological split

\[
 D(Y)=D_*\quad\text{or}\quad D(Y)>D_*.
\tag{3}
\]

The structure does **not** retain the actualizing subsequence.  Its producer
does: before compactification,

```text
target reward (packetProfile packet rank) (packet.mark rank) mover
```

is a literal one-date replacement of

```text
source reward (packetProfile packet rank).
```

Thus the reviewed forced-pair minimum-return construction can externally
retain a common source/replacement sequence.  Restoring that provenance is
mathematically meaningful, but it does not add the missing orientation below.

## 2. Maximum exact consequence in the minimum-target arm

Assume the restored common sequence

\[
 X_k=\operatorname{Sem}(\sigma_k)\to X,
 \qquad
 Y_k=\operatorname{Sem}(\sigma_k[m\leftarrow\tau_k])\to Y
\tag{4}
\]

and suppose `D(X)=D(Y)=D_*`.  For `0<s<1`, mix only player `m`'s complete
stopping law and let

\[
 Z_{k,s}=\operatorname{Sem}
 \bigl(\sigma_k[m\leftarrow(1-s)\sigma_{k,m}+s\tau_k]\bigr).
\]

After a compact subsequence, `Z_{k,s}->Z_s`.  Coordinatewise stopping-law
debt convexity gives

\[
 d_i(Z_s)\le(1-s)d_i(X)+sd_i(Y).
\tag{5}
\]

Summing (5), global minimality and `D(X)=D(Y)=D_*` force equality in the sum.
All coordinate gaps are nonnegative, hence equality holds coordinatewise:

\[
 \boxed{d_i(Z_s)=(1-s)d_i(X)+sd_i(Y).}
\tag{6}
\]

Therefore

\[
 \boxed{\operatorname{supp}_+d(Z_s)
 =\operatorname{supp}_+d(X)\cup\operatorname{supp}_+d(Y).}
\tag{7}
\]

This yields two honest finite-rank handoffs when their additional predicates
hold:

* if `Y` has a newcomer, `Z_s` is a minimum point with strictly larger
  support than `X`;
* if `Y` has no newcomer and `d_m(Y)=0<d_m(X)`, then `Y` has strictly smaller
  support than `X`.

The checked chord supplies only `d_m(Y)<=d_m(X)-a`.  It does not say
`d_m(Y)=0`.  Hence the third possibility—same full support and a positive
redistribution—remains.

The theorem in
`CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE.md` consumes the
second bullet after imposing both maximum support at `X` and complete mover
elimination at `Y`.  Neither is a field of `ThreeRoleLimitChord`.

## 3. Exact cyclic common-chord tableau

The following rational data satisfy every algebraic conclusion above while
admitting no support change or directed scalar rank.

Take four coordinates cyclically modulo four and put

\[
\begin{aligned}
d^0&=(2/5,1/5,1/5,1/5),\\
d^1&=(3/10,3/10,1/5,1/5),\\
d^2&=(3/10,1/5,3/10,1/5),\\
d^3&=(3/10,1/5,1/5,3/10).
\end{aligned}
\tag{8}
\]

Let `d^4=d^0` and repeat the four-state semantic word once more, so
`d^{k+4}=d^k` for `0<=k<=4`.  At step `k`, choose mover

\[
 m_k=k\pmod4
\]

and recipient `r_k=m_k+1 mod 4`.  Then

\[
 d_{m_k}^{k+1}=d_{m_k}^k-1/10,
 \qquad
 d_{r_k}^{k+1}=d_{r_k}^k+1/10,
\tag{9}
\]

and every other coordinate is unchanged.  Every vector is strictly positive
and has total debt one.

To retain the exact unilateral semantic identity, take one common cap vector

\[
 B^k=(1,1,1,1)
\]

and prescribed payoff `U^k=B^k-d^k`.  Then at every step

\[
 B_{m_k}^{k+1}=B_{m_k}^k,
 \qquad
 U_{m_k}^{k+1}-U_{m_k}^k=1/10,
\tag{10}
\]

so the mover's cap is unchanged and its debt drops exactly by its prescribed
payoff gain.  The recipient's cap is also unchanged while its prescribed
payoff drops by `1/10`, producing the debt rise.  Interpolate `U` affinely and
keep `B` constant on every displayed one-player chord.  Then debts are
coordinatewise affine, all proper chord points remain at total debt one, and
all have full positive support.

For Fin4, choose for example `lambda=1/2` and displayed minimum debt `D_*=1`.
The checked chord thresholds are

\[
 a=\frac{1}{32}<\frac1{10},
 \qquad
 b=\frac1{256}<\frac1{10}.
\tag{11}
\]

Choose at each step any owner distinct from the mover; the recipient is
already distinct from the mover.  Thus (1)--(3), (6), own-cap invariance, the
fixed mover drop and recipient rise, and exact source/replacement chord
affinity all hold.  Yet:

* positive support is always all four coordinates;
* total debt is always exactly the displayed global minimum one;
* every step has the required fixed transfer;
* after four steps the semantic state returns;
* no scalar debt or support rank decreases.

This is the exact signed-circulation obstruction.  One can attach an abstract
eight-edge Boolean profile word

\[
0000,1000,1100,1110,1111,0111,0011,0001,0000
\]

and repeat the four semantic vectors twice.  Each adjacent pair then differs
in one player's action and carries the corresponding cap-invariant transfer.
This records the full product-source provenance used by a one-player chord,
not merely detached endpoint labels.

Consequently no rank depending only on the retained semantic pair can
strictly decrease on every such chord: the semantic word already closes
after four edges.  Nor can a rank depending on the displayed source profile
and semantic pair do so on the eight-edge realization, whose profile and
semantic pair both return.  A successful well-founded theorem must therefore
retain and consume genuinely additional history or chronology; renaming the
ordered transfer roles as a state does not orient the cycle.

Again, this is an interface countermodel, not a quitting-game
counterexample.  The displayed carrier is the union of these chords; declaring
its objective minimum to be one is consistent with all retained compactness,
convexity, and transfer fields.  What is absent is precisely the additional
quitting-game chronology that the sought consumer would have to produce.

## 4. The strict-ascent arm has no quantitative charge

The mover and recipient inequalities do not give a positive lower bound on

\[
 D(Y)-D_*.
\]

Starting from any one step of (8), add an arbitrary `epsilon>0` to one
uninvolved target debt coordinate.  The mover drop and recipient rise remain
fixed while

\[
 D(Y)-D_*=\varepsilon.
\]

Thus the strict arm in (3) is qualitative only.  It cannot by itself fund a
uniform absorption charge, a finite debt decrement, or a real-valued
well-founded iteration.

The actual target sequence still supplies paid behavioral rows through the
ambient terminal witness, but the checked paid-cap trichotomy can end in the
same inert all-Continue stall.  That is additional machinery, not a consumer
encoded by the chord.

## 5. Verdict

`ThreeRoleLimitChord` is a correct compact transfer certificate but not a
standalone capstone.  Restoring the actualizing sequence upgrades it to an
exact common stopping-law chord and proves (6)--(7); it still leaves the
full-support circulation (8)--(10).  Therefore none of the following follows
from the stated inputs alone:

* minimum-fiber support/rank descent;
* a positive lower bound on strict target ascent;
* a cumulative Nash--Bellman return; or
* terminal approximants.

A valid downstream theorem must use one additional operation that is absent
from the interface: full mover elimination, maximum-support source selection,
an exact chronological charge, or source-regenerated control of the next
transfer.  Merely retaining the packet subsequence does not supply it.

This no-go does not resolve the forced-pair atlas node.  It prevents the
already-checked compact chord from being mistaken for its consumer and shows
that the missing ingredient is genuinely vertical/chronological rather than
another finite-label extraction.

## 6. Sources inspected

* `ConcentratedCollisionFourRole.ThreeRoleLimitChord`,
  `exists_threeRoleLimitChord_of_frequently_packetTransferRoles`, and
  `packet_tailEscapeFrequently_or_threeRoleLimitChord` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`;
* `quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum`
  and minimum-fiber chord affinity in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
  TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
* `QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster` and its
  minimum-fiber support-drop results in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/
  MinimumFiberSupportDrop.lean`;
* `CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE.md` and its
  independent review; and
* `ATLAS_GATEKEEPER__COLLISION_MINIMUM_WHOLE_SOURCE_RETURN_SEAM.md` and the
  reviewed forced-pair exports.

## 7. Requested falsification

Please check whether the external actualization really supplies a common
complete-stopping-law chord after both compact subsequences, whether (6)
follows without an attainment assumption, and whether any checked field
forces endpoint mover debt to zero.  A positive answer to the last question
would invalidate the tableau and activate the maximum-support support-drop
consumer.
