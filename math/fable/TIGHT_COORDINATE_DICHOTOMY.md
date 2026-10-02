# The tight-coordinate dichotomy at a unique-all-Continue cap

Author: CLAUDE_FABLE. Placement: the strict-inert arm of the
minimum-return consumer stores a carrier point \(y\) above the minimum
whose cap has uniquely-all-Continue exact Nash correspondence; the only
neighborhood consumer
(`eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap`,
`TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`) needs the
**strict** singleton gap \(s_i<c_i\) at every coordinate, while the
stored data give only \(s_i\le c_i\). The general off-minimum strict
moat is false: the pair of the sure-solo-quit profile by \(j\) has
\(c_j=s_j\) whenever \(s_j\ge0\). The correct local statement is a
dichotomy.

Notation: cap \(c\), solos \(s_i=r_i(\{i\})\), tight set
\(Z=\{i: s_i=c_i\}\), collision entry
\(C_{k,i}=r_k(\{i,k\})-r_k(\{i\})\)
(`quittingCollisionMatrix reward k i`, `Quitting/Root/FirstOrderProductFlow.lean`).
All statements are one-shot: about exact Nash roots against a fixed
continuation vector \(c\) (`IsεQuittingRootNash reward c 0`), no
carrier, no minimality.

**Theorem A (tight coordinates recruit tight eager joiners).** Suppose
\(s\le c\) pointwise and every exact Nash root against \(c\) is
all-Continue. Then for every \(i\in Z\) there is \(k\in Z\setminus\{i\}\)
with \(C_{k,i}>0\).

**Corollary B (dichotomy).** At such a cap, either \(Z=\emptyset\) —
the strict singleton gap holds at every coordinate — or \(|Z|\ge2\) and
the digraph on \(Z\) with edges \(i\to k\) when \(C_{k,i}>0\) has
positive out-degree at every vertex (hence contains a cycle).

**Corollary C (uniform gap).** If moreover no ordered pair of distinct
tight coordinates has a positive collision entry, then
\(\exists\delta>0:\ \forall i,\ \delta\le c_i-s_i\) — exactly the
missing hypothesis of the neighborhood-propagation theorem.

## Attribution (post-formalization audit)

Theorem A and the cycle of Corollary B are already checked and
integrated, in cap-defect/collision-gain vocabulary and without any
reward bound: `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`
(`Quitting/Punishment/SingletonCapBindingCollision.lean`) and
`exists_quittingSingletonCapBindingCollisionCycle`
(`Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`), with
`quittingSingletonCapDefect reward cap who = 0` as tightness and
`quittingSingletonCollisionGain reward i k = C_{k,i}` (index swap:
`quittingCollisionMatrix reward k i`). The scratch file delegates to
them through the bridge
`fable_quittingCollisionMatrix_eq_singletonCollisionGain`. The
genuinely new content is Corollaries C1/C2: the strict and uniform
singleton gaps under the no-tight-eager-pair hypothesis, which feed the
neighborhood-propagation theorem. The proof below is kept as the
ordinary-math record of the (re-derived) core argument.

## Proof of Theorem A

Fix \(i\in Z\) and suppose no \(k\in Z\setminus\{i\}\) has
\(C_{k,i}>0\). Let \(M\) bound all rewards,
\(\delta=\min\{c_k-s_k: k\notin Z\}\) (positive if the set is
nonempty), and

\[
p=\begin{cases}\delta/(\delta+2M+1)&\{k:k\notin Z\}\ne\emptyset\\
1/2&\text{otherwise,}\end{cases}
\qquad p\in(0,1).
\]

Let \(\rho\) be the root in which \(i\) quits with probability \(p\) and
every other player continues surely. Check the exact endpoint-Nash
conditions (for each player: continue-prob times the Quit-minus-Continue
endpoint difference \(\le0\), and quit-prob times it \(\ge0\);
equivalent to exact Nash by
`isεQuittingRootEndpointNash_iff_isεQuittingRootNash`):

- Player \(i\): pure quit yields \(s_i\) (others continue surely), pure
  continue yields \(c_i\); the difference is \(s_i-c_i=0\) by tightness,
  so both conditions hold with equality.
- Player \(k\ne i\): quit-prob is zero, so only the continue-side
  condition binds: the difference is
  \[
  \bigl[p\,r_k(\{i,k\})+(1-p)s_k\bigr]-\bigl[p\,r_k(\{i\})+(1-p)c_k\bigr]
  =p\,C_{k,i}-(1-p)(c_k-s_k).
  \]
  If \(k\in Z\): \(c_k=s_k\) and \(C_{k,i}\le0\) by assumption, so the
  difference is \(\le0\). If \(k\notin Z\): \(C_{k,i}\le2M\) and
  \(p(2M+1)\le(1-p)\delta\le(1-p)(c_k-s_k)\) by the choice of \(p\), so
  the difference is \(<0\).

Thus \(\rho\) is an exact Nash root against \(c\) with
\(\rho_i(\text{quit})=p>0\), so \(\rho\ne\) all-Continue —
contradicting uniqueness. ∎

Corollary B is immediate (finite positive-out-degree digraphs contain
cycles). Corollary C: each coordinate is non-tight by Theorem A, and the
minimum of finitely many positive gaps is positive. ∎

## Consequences for the strict-inert residual

The stored uniqueness datum now splits the strict-inert arm:

1. **no tight eager pair** — Corollary C supplies the uniform
   \(\delta\), the neighborhood-propagation theorem applies, and the
   uniqueness plateau survives cap perturbations below \(\delta\); or
2. **a tight eager cycle inside \(Z\)** — at least two players sit
   exactly at their solo value at an off-minimum point, each recruited
   by another (\(C_{k,i}>0\) along a cycle). This is collider structure
   (dossier R4) transported off the minimum, now with exact equalities
   \(s_k=c_k\) on the cycle — a far sharper residual than the bare
   uniqueness datum, and the natural interface to the forced-pair
   machinery.

Status: kernel-checked in the scratch lane
(`lean/FableTightCoordinateDichotomy.lean`; independently verified: clean
compile, lexical scan clean, axioms propext/Classical.choice/Quot.sound
only; re-verified after the delegating refactor, 143 lines).
