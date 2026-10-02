# Recentered marked hazard kernels

**Status:** corrected ordinary-mathematics reduction; independently audited.
It is a representation theorem, not a Fin4 consumer.

**Source prompt:** `fable/NONLOCAL_RECENTERING_ATTACK.md`.

**Independent review:**
`feedback/NONLOCAL_RECENTERING_ATTACK__BY_CODEX_ADVERSARY.md`.

**Additional review:**
`feedback/NONLOCAL_RECENTERING_ATTACK__BY_CODEX_ROOT.md`.

## Question

What relative-timing information survives if actual quitting profiles are
recentered at cofinally reached marked dates before compactification?

## Corrected result

Let `sigma_n` be behavioral profiles and let `tau_n -> infinity` be marked
dates with unconditional survival to `tau_n` at least `lambda > 0`.  Recenter
the live hazard rows at `tau_n` and extract one pointwise-convergent
subsequence on every integer offset.  Its limit `y : Z -> [0,1]^I` satisfies

\[
 \sum_{t<0}\sum_i y_{t,i}\le \log(1/\lambda).
\]

Thus its negative-time half is summable.  If `kappa^(s)` starts at row `-s`
of this two-sided array, then its prescribed payoffs and terminal laws are
Cauchy as `s -> infinity`.  Its unrestricted behavioral caps are also Cauchy.
The latter uses the corrected pair of estimates, for `s' > s >= 1`,

\[
 \left|B_i(\kappa^{(s')})-
 \max\{B_i(\kappa^{(s)}),r_i(\{i\})\}\right|
 \le 4R\delta_s,
\]

and

\[
 B_i(\kappa^{(s)})
 \ge r_i(\{i\})-2R\delta_{s-1},
 \qquad
 \delta_s:=\sum_{t<-s}\sum_i y_{t,i}.
\]

Consequently the limiting semantic pair lies in the closed carrier and its
cap satisfies `b_i >= r_i({i})` for every player.  All Continue is therefore
an exact root against this limiting cap.

If, at every marked date, one fixed terminal coalition has unconditional
stage mass at least `lambda`, then every negative truncation of the kernel
retains that coalition at recentered date zero with mass at least
`lambda^2`.

For marked dates not known to diverge, first extract a subsequence on which
they are constant or tend to infinity.  The bare summability conclusion also
holds in the constant case because of zero padding, but only the divergent
case gives arbitrarily deep literal pre-mark provenance.  The concrete
source-preserving Fin4 frames appear to provide divergence through their
strictly increasing source ranks and stage/stack bounds; that adapter has not
been packaged here.

## What is new and what is not

The general centered-window extraction overlaps
`Math.Topology.SourceOmegaChain` in `MathUE/Topology/SourceOmegaChain.lean`.
The additional content is:

- the logarithmic negative-hazard bound forced by a reach floor;
- convergence of the actual terminal payoff/law semantics of negative
  truncations; and
- the repaired unrestricted-cap boundary semantics.

The affine one-owner stationary covering screen in the source prompt is also
correct and useful for candidate-table filtering, but is logically separate
from the kernel theorem.

## What this does not prove

Pointwise convergence on nonnegative offsets does not transport future
terminal semantics or unrestricted caps; mass may escape to later dates or
Never.  More decisively, reapplying a minimum-source producer after a return
may select an unrelated realizing chronology.  Uniform reached-mass and paid-
gain floors do not place the next mark later in the same source history.

To obtain a multi-mark kernel one still needs a source-faithful renewal
theorem which constructs each next mark as a literal later continuation of
the same ancestry, with common finite-depth subsequences and suitable
conditional error control.  Only then could an inverse-limit argument place
all marks in one kernel.

Hence the strongest present implication is

\[
 \text{cofinally reached marked source}
 \Longrightarrow
 \text{one marked kernel with an inert summable past},
\]

not a two-port recurrence, charged return, or uniform-equilibrium compiler.

## Failed literal statement retained

The source draft stated the cap comparison for `s' >= s`.  Equality is false:
with no hazards before row `-1`, an opponent hazard `1/2` at row `-1`, solo
reward `1`, and both relevant opponent/collision rewards `0`, one has
`delta_1=0` but `B_i(kappa^(1))=1/2`.  The strict inequality `s'>s` and the
separate solo lower bound above are essential.

## Next concrete question

Can the actual Fin4 minimum-return ancestry produce a second marked row later
in the same realizing profile, with a uniform positive reach floor and
conditional semantic error tending to zero?  A positive answer would turn
this one-mark representation into a genuine source-faithful multi-mark
kernel; compactness alone cannot do so.
