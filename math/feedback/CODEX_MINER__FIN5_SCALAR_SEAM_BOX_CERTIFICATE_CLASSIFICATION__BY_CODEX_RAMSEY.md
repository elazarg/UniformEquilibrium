# Independent review of the Fin5 scalar seam/box classification

Reviewer: `CODEX_RAMSEY`

Source reviewed:
[`CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION.md`](../notes/CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION.md)

Repository head audited: `29a172f34a919f925bd1109a55c75c9a55d4078c`

## Verdict

**PASS as ordinary mathematics in its stated internal supplied-root scope.**
The one-scalar elimination, exact redundancy of the canonical payoff-box
rows, impossibility of seam-only infeasibility, completeness of the three
certificate types, and the rational phase--seam arithmetic all check.

One provenance qualification is important.  The printed table gives literal
quiet-face roots with positive nonempty opponent atoms, and those roots can be
completed individually to actual exact deleted-game suffixes.  It does **not**
give the positive omitted-player outward gap on every face: every coordinate
other than player `0` is identically zero, and player `0` also has no positive
face-0 gap.  Thus Section 5 refutes elimination of phase--seam certificates by
scalar algebra, reward bounds, or atom floors; by itself it does not prove
that the full reviewed codimension-one producer can realize the pattern.

I found a rational coordinatewise completion which supplies that stronger
local face provenance while retaining the same phase--seam obstruction.  It
is new mathematics and is recorded separately rather than being inserted
into this review or the author's note.

No existing phase--seam consumer follows from the reviewed scalar fields.
At the exact cyclic fixed point a crossing merely localizes a supported
one-row regret; it does not produce a Bellman edge, floor admissibility,
source return, rank decrease, or terminal contradiction.

## 1. Exact scalar elimination

For one payoff coordinate and a fixed root `x^t`, the Bellman map is

\[
 F_t(z)=a_t+\beta_tz,
 \qquad 0\le\beta_t\le1,
 \qquad |a_t|\le M(1-\beta_t).
\]

With cut variable `x=v_0(i)`, exact propagation at phases `4,3,2,1` makes
every other scalar value affine in `x`.  The closing composite is

\[
 \Phi(x)=A+Bx,qquad B=\prod_t\beta_t\in[0,1].
\]

The two seam rows are exactly `|x-Phi(x)|<=delta`.

For player `i`, the Quit-minus-Continue endpoint difference is

\[
 G_{i,t}(z)=c_{i,t}-m_{i,t}z,
\]

because only the all-opponents-Continue event reaches the continuation.  The
two supported-action regret inequalities are

\[
 p^C_{i,t}G_{i,t}(v_{t+1})\le\varepsilon,
 \qquad
 -p^Q_{i,t}G_{i,t}(v_{t+1})\le\varepsilon.
\]

After substitution they are affine rows in `x`.  This is exactly equivalent
to `IsεQuittingRootEndpointNash`, hence to unrestricted one-root mixed
deviations.  Each coordinate uses only its own continuation scalar, so the
five scalar solutions may be recombined for the same common roots.

The note correctly restricts this reduction to exact propagation at four
phases.  Five independent Bellman-error variables would not reduce to one
cut scalar without further elimination.

## 2. Canonical payoff-box rows

If `|z|<=M`, then

\[
 |F_t(z)|\le |a_t|+\beta_t|z|
 \le M(1-\beta_t)+M\beta_t=M.
\]

Thus `x in [-M,M]` propagates every scalar value inside the same interval.
The intermediate `quittingNashBellmanBox` rows are true throughout the cut
domain and cannot occur in a minimal certificate.  This remains correct at
`M=0`: normalization by `x(w)=(1-w)(-M)+wM` becomes constant but still
parametrizes the singleton domain sufficiently for feasibility.

This argument is exact.  It does not remove punishment-floor, target-window,
or other externally imposed bounds, and it would need an enlarged box if
Bellman errors were propagated rather than isolated at the seam.

## 3. Seam feasibility and certificate completeness

The composite `Phi` maps `[-M,M]` into itself.  If `B<1`, its unique fixed
point is `A/(1-B)` and lies in the interval.  If `B=1`, all five `beta_t` are
one and all five `a_t` vanish, so `Phi` is the identity.  Therefore the two
seam rows are jointly feasible for every `delta>=0`.

Applying `Math.finiteAffineIntervalFeasible_iff` to endpoint evaluations on
the canonical interval gives precisely:

1. one row positive at both endpoints; or
2. one decreasing and one increasing row violating the cross-product test.

Every inclusion-minimal infeasible subsystem therefore has size at most two.
After removing the redundant box rows and the jointly feasible seam-only
systems, the possible types are exactly:

- one phase row;
- two phase rows; or
- one phase row and one seam row.

There is no missing seam-singleton or seam--seam case.  Encoding the canonical
domain as rows inside a larger artificial interval can create box crossings,
but those are normalization artifacts exactly as the note states.

## 4. Rational Fin5 phase--seam example

The example's calculations are exact.

- `q_t=(2,3,4,2,1)` always differs from phase owner `t`, so each root lies on
  the stated quiet face.
- Exactly `q_t` Quits with probability `1/2`, giving the nonempty
  opponent-only atom `{q_t}` of mass `1/2`.
- Player `0` Continues surely, all singleton payoffs in its coordinate are
  zero, and hence every Bellman map is `F_t(z)=z/2`.
- Exact propagation gives
  `v_4=x/2`, `v_3=x/4`, `v_2=x/8`, `v_1=x/16`, and
  `Phi(x)=x/32`.
- At phases `0,1,2,3`, player `0`'s supported Continue row only asks for a
  successor at least `-1`, which is automatic on the canonical box.
- At phase `4`, the row is `x>=1`.

At `delta=0`, the normalized phase row has endpoint values `(1,0)` and the
upper seam row has `(-31/32,31/32)`, so their cross product fails.  For
general `delta`, the seam upper endpoint is `31/32-delta`; the same minimal
crossing persists exactly for

\[
 0\le\delta<31/32.
\]

At `delta=31/32`, `x=1` is feasible, so the threshold is sharp.

The other payoff coordinates are zero, so their Bellman and endpoint rows at
the zero annotation are exact.  There is no hidden unrestricted-deviation
issue: endpoint Nash is equivalent to every mixed unilateral root deviation.

### Literal reached-face realization

The roots are more than abstract affine rows.  Phases `0` through `3` can be
followed by literal all-Never, giving exact deleted-game suffixes because all
survivor coordinates are zero except player `0`, whose displayed pair rows
make Continue optimal when it is retained.  At phase `4`, follow survival by
the pure coalition `{0,1}`: player `0` obtains continuation `1`, player `1`
is indifferent at zero, and all other coordinates are zero.  This realizes
the phase-4 threshold and is an exact deleted-game suffix.

However, none of these sources has the codimension-one omitted-player
positive-gap field.  This is the precise source boundary, not a defect in the
phase--seam calculation.

## 5. Source and novelty audit

The cited declarations have the stated roles:

- `quittingRootExpectedPayoff_eq_absorbingContribution_add` supplies the
  affine Bellman map;
- `IsεQuittingRootEndpointNash` supplies the two supported rows;
- `abs_quittingRootExpectedPayoff_le_bound` supplies exact cube preservation;
- `finiteAffineIntervalFeasible_iff` supplies the one-/two-row certificate;
  and
- the periodic compiler and cycle-mismatch results begin after compatible
  endpoint-Nash/Bellman data are supplied and do not remove this crossing.

The only nearby checked use of the interval theorem is unrelated collision
rate elimination.  I found no duplicate cyclic seam classification.

## 6. Consumer assessment

At `B<1`, a phase--seam crossing says exactly that some supported phase row is
violated at the unique actual cyclic Bellman value (quantitatively so when
the crossing has a margin).  This is a local regret certificate for the
periodic profile.  The terminal exploitability floor already predicts that
some coordinate of every profile is exploitable; it does not turn this
localization into a contradiction.

In particular the scalar certificate does not retain:

- a common actual source with the five face continuations;
- a punishment-floor Nash--Bellman edge;
- a paid return or cumulative charge;
- a strict debt/support rank decrease; or
- a checked sure-exit/uniform-payoff compiler.

Accordingly there is no further consumer from the stated fields alone.  The
next genuine producer question is whether the *full* reached quiet-face
outward-gap provenance constrains the phase--seam pattern.  The author's
printed example leaves that question open; the separate completion found in
this review addresses it at the local-source level only, not under a global
positive-minimum counterexample hypothesis.

## Recommendation

Retain internally and do not export without a new consumer and packet gate.
If formalized, package the exact-propagation scalar classification separately
from the Fin5 regression, with the canonical-domain normalization explicit.
