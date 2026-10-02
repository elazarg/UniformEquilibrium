# A normalized-passport minimizer eliminates support entry

Author: FORCED_PAIR_REVIEW

## Status

The support-entry half of the off-minimum maximal-ray stall can be eliminated
by changing the selection principle.

The correct state is not the terminal semantic/law point alone. It is a
compact decorated point retaining:

* the whole semantic pair and terminal law;
* the literal semantic/law tail after a fixed pure pair;
* the transported mass of that marked pair;
* the transported paid gain;
* the fixed pair, owner, mover, and orientation labels; and
* provenance from the original forced-pair source under arbitrary finite
  literal prefixes.

Take the closure of all such finite-prefix descendants. Prefixing by a fixed
root is a continuous self-map of this decorated carrier. On an exact
cap--Nash prefix, whole debt, marked mass, and paid gain all scale by the same
joint Continue factor. Therefore the two normalized density inequalities

\[
m\ge\theta D,
\qquad
g\ge\psi D
\]

define a compact prefix-invariant slice.

Minimize whole debt on that slice. If the minimum is \(D_*\), actualizers of
the decorated minimizer form the maintained minimum-return pair packet and
feed the existing three-role compiler. If the minimum is greater than
\(D_*\), every exact cap--Nash root at the decorated minimizer must be all
Continue: any positive-absorption root would remain inside the same slice
and strictly lower debt, contradicting minimality.

Thus the support-entry arm is consumed. The surviving obstruction is a
source-attached normalized-passport minimizer whose exact root correspondence
is uniquely all Continue.

This is ordinary mathematics. The topology and prefix identities are
compositions of checked results, but the decorated carrier and capstone are
not yet Lean declarations.

## 1. Why an ordinary infimum is insufficient

Suppose a source with whole debt \(L>D_*\) admits a support-entry root with
survival \(c<1\). Prefixing lowers the limiting debt to \(cL\), while
preserving pair-mass/debt and paid-gain/debt ratios. A naive infimum over
source packets almost works, but two issues must be handled:

1. the amount \((1-c)L\) may depend on the selected source and tend to zero
   along a minimizing sequence; and
2. the set of literal source packets with a fixed positive density threshold
   need not be closed, because a fixed root is only approximately Nash on
   prelimit actualizers.

Choosing an approximate minimizer cannot solve the first issue without a
uniform drop. Shrinking density thresholds at each restart would solve the
second only at the cost of destroying invariance.

The repair is to minimize on a **closed decorated carrier slice**, not on the
raw actual packets. Exact prefixing acts on the limit point, where all three
quantities scale exactly. No uniform debt drop and no threshold degradation
are needed.

## 2. Raw marked-pair data

### Source-facing adapter

The local checked adapter is
`FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket`, whose
output `FinFourWeakCoreForcedPairPacket` records the literal pair, zero-defect
forced owner, distinct positive-defect payer, fixed mass floor, exact paid
gain, and unchanged post-date live-root tail.  In the minimum-law singleton
route, the cofinal source chronology is the checked
`FinFourOwnerCompressedSingletonProducer`; its endpoints and strong packets
are supplied by
`FinFourOwnerCompressedSingletonProducer.nonempty_strongConcentratedPacket`.

The fixed-label moving family used below is the source-facing mathematical
corollary recorded in
`FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md`, followed by the strict
canonical-ray stall arm of
`FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`.  That composition has not
yet been packaged as one Lean declaration.  Before defining the orbit, take
the finite pigeonhole subsequence on which the pair, forced owner, payer, and
endpoint orientation are all fixed.  No later minimization reselects these
labels or the original minimum source.

Fix a Fin4 reward table and fixed labels

\[
C=\{j,o\},
\qquad
p\ne o.
\]

Assume the table-level pure-pair data satisfy:

* the marked owner \(o\) has zero local root defect at \(C\); and
* the selected mover has a fixed positive pure-pair endpoint gain
  \(\delta_p>0\).

These are tail-independent because \(|C|=2\): after any unilateral endpoint
change at the pair, at least one player still Quits surely.

A raw decorated datum consists of an actual behavioral profile \(X\), a
marked date \(t\), and the tuple

\[
\mathcal A(X,t)
=
(z,\nu,w,\omega,m,g),
\tag{1}
\]

where:

* \(z=\operatorname{Sem}(X)\);
* \(\nu=\operatorname{Law}(X)\);
* the live root of \(X\) at \(t\) is the pure pair \(C\);
* \(w\) is the complete terminal-semantic pair of the all-Continue spine
  strictly after \(t\);
* \(\omega\) is its complete terminal law;
* \(m\) is the unconditional mass of \(C\) at date \(t\); and
* \(g=m\delta_p\) is the whole-profile payoff gain of the selected one-date
  endpoint update.

The whole gain identity is exact, and changing only \(p\)'s complete strategy
subtracts \(g\) exactly from \(p\)'s unrestricted terminal debt.

Let

\[
 (X_n,t_n)\qquad(n\in\mathbb N)
\]

be the one fixed-label cofinal forced-pair family selected before this
construction.  Thus the pair $C$, zero-defect owner $o$, paid mover $p$,
and endpoint orientation do not depend on $n$.  For every length
$k\in\mathbb N$, let a word be an arbitrary tuple

\[
 W=(q_0,\ldots,q_{k-1})
\]

of product roots; no Nash condition is imposed on any $q_h$.  Write
$W\triangleright X_n$ for their literal chronological prefix and
$s(W)=\prod_{h<k}\operatorname{Cont}(q_h)$.

A descendant of \((X_n,t_n)\) by \(W\) is

\[
(W\triangleright X_n,\ t_n+k).
\]

The post-pair tail remains literally the old tail. If

\[
s(W):=\Pr_W(\text{every prefixed root Continues}),
\]

then

\[
m(W\triangleright X_n)=s(W)m(X_n),
\qquad
g(W\triangleright X_n)=s(W)g(X_n).
\tag{2}
\]

Explicitly, the raw orbit is

\[
 \mathcal R
 :=
 \left\{
   \mathcal A(W\triangleright X_n,t_n+|W|):
   n\in\mathbb N,\ |W|<\infty
 \right\},
\]

where $W$ ranges over **all** finite product-root words.  Thus
$\mathcal R$ is a union over every original source rank and every finite
literal prefix, rather than the orbit of one independently selected carrier
point.

## 3. The compact decorated carrier

It is useful to make the ambient space and the closure convention explicit.
Regroup (1) as

\[
 ((z,\nu),(w,\omega),m,g).
\]

Both \((z,\nu)\) and \((w,\omega)\) belong to the checked compact joint
semantic/law carrier.  The mass belongs to \([0,1]\).  If \(M\) is the
canonical reward bound, then \(0\le g\le 2M\): the selected endpoint gain is
nonnegative, its conditional reward difference is at most \(2M\), and its
unconditional live mass is at most one.  Thus every raw datum belongs to the
compact product

\[
 \mathcal J_r\times\mathcal J_r\times[0,1]\times[0,2M],
\tag{3}
\]

where \(\mathcal J_r\) is the joint semantic/law carrier.  Define

\[
\mathcal K:=\overline{\mathcal R}
\tag{4}
\]

with closure taken inside this ambient product.  Equivalently one may take
ordinary closure in the surrounding finite Euclidean product, because (3) is
compact and hence closed.  Therefore \(\mathcal K\) is compact.

Here \(\mathcal R\) contains descendants by **all** finite literal product-root
words, not only exact or maximal cap--Nash words.  This point is essential:
the positive-absorption root selected later at a carrier limit need not be
exact at any raw approximant.  Its literal prefixes must nevertheless already
belong to the raw orbit whose closure defines \(\mathcal K\).

For a fixed product root \(q\), define the decorated prefix map

\[
\Phi_q(z,\nu,w,\omega,m,g)
:=
(T_qz,\ P_q\nu,\ w,\omega,\ cm,\ cg),
\tag{5}
\]

where \(c=\operatorname{Cont}(q)\).

The semantic prefix, affine law prefix, and scalar multiplications are
continuous. On every raw datum, (5) is exactly the tuple of the literal
profile \(q\triangleright X\) at marked date \(t+1\). The raw orbit was
defined to be closed under that operation. Therefore continuity gives

\[
\boxed{\Phi_q(\mathcal K)\subseteq\mathcal K}
\tag{6}
\]

for every fixed product root \(q\).

This is the source-provenance field absent from an ordinary joint
semantic/law point. The tuple remembers the counterfactual tail and the
transported marked mass even when the marked dates escape to infinity.

The compactness claim uses no compactness of stopping laws.  It uses the
already compact joint semantic/law carrier twice and two bounded scalar
coordinates.  Relative timing may disappear from a carrier limit, but the
two scalar marked quantities survive as explicit coordinates.

## 4. Fixed normalized-passport slices

Let \(D_*>0\) be the global minimum total debt. Fix constants

\[
\theta>0,
\qquad
\psi>0.
\]

Define the normalized-passport slice

\[
\mathcal K_{\theta,\psi}
:=
\left\{
(z,\nu,w,\omega,m,g)\in\mathcal K:
\begin{array}{l}
D(w)=D_*,\\
m\ge\theta D(z),\\
g\ge\psi D(z)
\end{array}
\right\}.
\tag{7}
\]

All three conditions are closed, so this slice is compact.

It is nonempty for suitable positive thresholds.  This must use one
simultaneous decorated cluster, rather than separately selected semantic and
law limits.  Start with the retained fixed-label forced-pair family before
adding any new prefix.  Along the source subsequence its post-pair joint
semantic/law points converge to a minimum-fibre point.  Compactness of the
ambient product then gives a further subsequence on which the whole joint
points and the two bounded marked scalars converge simultaneously.  The
resulting point belongs to \(\mathcal K\), because the empty prefix word is
allowed.  The retained mass and paid-gain floors give

\[
D(z)=L>0,
\qquad
m>0,
\qquad
g>0,
\qquad
D(w)=D_*.
\]

Choose, for example,

\[
0<\theta<{m\over L},
\qquad
0<\psi<{g\over L}.
\tag{8}
\]

The strict choice is convenient only for later raw actualizers. The carrier
argument itself also works at equality.

## 5. Exact prefix invariance of the slice

Take

\[
x=(z,\nu,w,\omega,m,g)\in\mathcal K_{\theta,\psi}
\]

and let \(q\) be exact cap--Nash against \(z^B\). Put
\(c=\operatorname{Cont}(q)\).

Exact cap--Nash debt scaling gives

\[
D(T_qz)=cD(z).
\tag{9}
\]

By (5), the new marked quantities are

\[
m'=cm,
\qquad
g'=cg.
\tag{10}
\]

The tail coordinates \(w,\omega\) are unchanged. Hence

\[
m'=cm\ge c\theta D(z)=\theta D(T_qz),
\tag{11}
\]

and similarly

\[
g'\ge\psi D(T_qz).
\tag{12}
\]

Combining (6), (11), and (12),

\[
\boxed{
x\in\mathcal K_{\theta,\psi}
\ \wedge\
q\in\operatorname{Nash}(z^B)
\Longrightarrow
\Phi_q(x)\in\mathcal K_{\theta,\psi}.
}
\tag{13}
\]

The normalized class is exactly invariant. No threshold shrinks.

The approximate-root errors on raw actualizers do not affect this statement:
(13) is applied at the decorated carrier point where \(q\) is exact. The
literal \(q\)-prefixes of raw approximants establish membership in
\(\mathcal K\); the exact scaling at the limit establishes the density
inequalities.

More explicitly, if \(x_n\in\mathcal R\) tends to \(x\), then the literal
profiles defining \(\Phi_q(x_n)\) are still elements of \(\mathcal R\), even
when \(q\) has positive Nash defect against the cap of every \(x_n\).  By
continuity they tend to \(\Phi_q(x)\).  Exactness is used only after taking
the limit, in (9), and never asserted for the raw prefixes.

### Finite-source density-loss boundary test

This limit-carrier formulation is necessary.  Suppose $q$ is exact only at
the limiting cap and has total root defect $E_n>0$ against a raw source
$X_n$.  The finite exact account is

\[
 D(q\triangleright X_n)=cD(X_n)+E_n,
 \qquad m(q\triangleright X_n)=cm_n,
 \qquad g(q\triangleright X_n)=cg_n.
\]

If a finite source saturates $m_n=\theta D(X_n)$, then

\[
 \frac{cm_n}{cD(X_n)+E_n}<\theta.
\]

For the scalar test $D(X_n)=1$, $c=1/2$, $m_n=\theta$, and
$E_n=1/n$, every finite prefix lies outside the weak density class even
though its density tends to $\theta$.  A subsequent exact prefix cannot
repair this loss because it scales numerator and denominator equally.

This falsifies the stronger but tempting assertion that the raw actual packet
class is itself prefix-invariant.  The theorem claims only that the **closed
decorated carrier slice** is invariant: the approximate literal prefixes
establish carrier membership, while the defect disappears exactly at the
limit root where (9) is applied.

## 6. Debt minimization eliminates support entry

Because \(\mathcal K_{\theta,\psi}\) is nonempty and compact, total whole
debt attains its minimum. Choose

\[
x_0=(z_0,\nu_0,w_0,\omega_0,m_0,g_0)
\in\mathcal K_{\theta,\psi}
\]

with

\[
\overline D:=D(z_0)
=
\min_{x\in\mathcal K_{\theta,\psi}}D(x.z).
\tag{14}
\]

Global minimality gives

\[
\overline D\ge D_*>0.
\tag{15}
\]

Let \(q\) be any exact cap--Nash root against \(z_0^B\), and put
\(c=\operatorname{Cont}(q)\). By (13), \(\Phi_q(x_0)\) belongs to the same
slice. Minimality and exact scaling give

\[
\overline D
\le D(T_qz_0)
=c\overline D
\le\overline D.
\tag{16}
\]

Thus equality holds throughout. Since \(\overline D>0\),

\[
c=1.
\tag{17}
\]

A product root has joint Continue mass one only when every player Continues
surely. Therefore

\[
\boxed{
\forall q\in\operatorname{Nash}(z_0^B),
\qquad q=\mathbf C.
}
\tag{18}
\]

All Continue is itself exact at every carrier cap: each cap coordinate
dominates the immediate singleton-Quit payoff because that pure deadline is
among the unrestricted deviations used to define the cap.  Therefore the
exact root correspondence at the normalized-passport minimizer is not empty
and is exactly the singleton set containing all Continue.  Equivalently, every
exact root has zero absorption, and for a product root this is equivalent to
being literally all Continue.  The positive-absorption support-entry arm is
impossible.

This argument applies to every exact root, not merely the maximal selector.

## 7. The minimum-return arm

Suppose

\[
\overline D=D_*.
\tag{19}
\]

Because \(x_0\in\mathcal K=\overline{\mathcal R}\), choose raw finite-prefix
descendants converging to \(x_0\). Their:

* whole debts converge to \(D_*\);
* post-pair tail debts converge to \(D_*\);
* pair masses converge to
  \(m_0\ge\theta D_*>0\); and
* paid gains converge to
  \(g_0\ge\psi D_*>0\).

Hence, after deleting finitely many terms, they carry fixed positive mass
and gain floors, the same pair/owner/mover labels, exact post-pair tail
provenance, zero marked-owner defect, and exact mover debt subtraction.

This is precisely the whole-source-return concentrated pair packet consumed
by the existing Fin4 three-role transfer/limit-chord compiler.

The use of strict thresholds in (8) ensures that actualizers may lose an
arbitrarily small amount in the inequalities while retaining, for example,
\(\theta D_*/2\) and \(\psi D_*/2\) as fixed literal floors.

There is one minor chronological normalization.  A sequence supplied by
membership in the closure need not have increasing marked dates.  Recursively
choose an all-Continue prefix length $N_n$ so that the shifted $n$-th mark is
strictly later than the preceding shifted mark.
This changes none of its decorated coordinates, whole semantics, whole law,
tail, marked mass, or marked gain, but shifts the marked date by $N_n$.
Taking
cutoff equal to mark plus one and scale $1/(n+1)$ gives the standard
concentrated packet:

* its whole source debts tend to $D_*$;
* its marked pair mass has a fixed positive floor;
* its marked owner defect is identically zero, hence its normalized defect is
  identically zero; and
* its marked tails tend to the minimum-fibre tail coordinate $w_0$, so the
  fixed positive tail-escape arm is eventually impossible.

Thus this arm uses actual behavioral profiles at every rank.  It does not
identify the carrier minimizer itself with an attained profile.

## 8. The off-minimum arm

If

\[
\overline D>D_*,
\tag{20}
\]

the selected decorated point carries:

* a fixed positive normalized pair passport;
* a fixed positive normalized paid passport;
* a minimum-debt post-pair tail; and
* unique all-Continue exact cap root.

Thus the previous support-entry alternative contracts to

\[
\boxed{
\text{minimum-return three-role output}
\quad\lor\quad
\text{normalized-passport unique-all-Continue minimizer}.
}
\tag{21}
\]

No positive-absorption exact root remains to restart.

This does not consume the unique-all-Continue branch. The pair atom and paid
row are stored in the counterfactual marked suffix, while every fresh exact
root at the selected outer cap is all Continue. The new content is that
support entry cannot recur indefinitely or require a real-valued descent
argument.

## 9. Why the decorated state is necessary

The ordinary joint point \((z,\nu)\) does not determine the post-pair tail or
the origin of the pair mass. A pure nonsingleton root followed by two
arbitrary tails has the same whole semantic pair and terminal law, while the
counterfactual tails differ.

Therefore a class defined only by \(D(z)\), \(\nu(C)\), and fixed labels is
not source-faithful enough for the downstream compiler. The decorated tuple
stores exactly the additional finite-dimensional data used by literal
prefixing:

\[
(w,\omega,m,g).
\]

No full stopping law or unbounded chronology is needed after passing to its
compact orbit closure.

## 10. Lean-facing target

### Checked source audit

The following declarations were inspected narrowly.

* `FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket` and
  the `FinFourWeakCoreForcedPairPacket` projections in
  `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean` provide the
  checked local pair, owner, payer, mass, gain, and tail identities.
* `FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer` and
  `FinFourOwnerCompressedSingletonProducer.nonempty_strongConcentratedPacket`
  in the minimum-clock and strong-packet modules provide the checked fixed
  chronology on the singleton source arm.
* `quittingTerminalSemanticLawCarrier_isCompact` and
  `quittingTerminalSemanticLawPoint_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`
  provide the compact joint carrier and its literal actual points.
* `continuous_quittingTerminalSemanticPrefix` and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` provide the
  continuous semantic action of a fixed root.
* `continuous_quittingTerminalOutcomeLawPrefix`,
  `quittingTerminalOutcomeLawPrefix_outcomeMass`, and
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `TerminalSemanticResetIncidenceReturn.lean` provide the continuous affine
  law action and its literal-profile provenance.
* `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`
  is the arbitrary-root debt account.  Exact cap--Nash means its nonnegative
  total-defect term is zero, yielding (9).
* `eq_pure_false_of_quittingStationaryContinueMass_eq_one` in
  `UniformEquilibrium/Quitting/Stationary/LiveMass.lean` is the product-root
  implication used after (17).
* `QuittingReprojectionConcentratedPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`
  is the actual packet constructed in the minimum-return arm.
* `ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer`
  and its fixed-role/limit-chord continuations in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean` are the
  checked consumers.  Their genuinely missing input was convergence of the
  whole packet-source debts to (D_*); the actualizers above provide exactly
  that input.

The only new topology is compactness of a closed subset of the finite product
of two already checked joint carriers and two compact intervals.  The only
new dynamics is closure under all finite literal root words and the two scalar
transport identities for marked mass and marked payoff difference.

Define a raw marked-pair tuple and its finite-prefix orbit, then:

~~~text
QuittingMarkedPairPrefixOrbitCarrier
QuittingMarkedPairNormalizedPassportSlice
~~~

The key declarations should be:

~~~text
markedPairPrefixOrbitCarrier_isCompact
markedPairPrefixMap_mem_carrier
markedPairPrefixMap_mass
markedPairPrefixMap_gain
markedPairNormalizedSlice_mem_prefix_of_capNash
exists_minimum_markedPairNormalizedSlice
minimum_markedPairNormalizedSlice_unique_allContinue
~~~

The final source theorem should return:

~~~text
minimumReturnConcentratedPair
or
offMinimumNormalizedPassportUniqueAllContinue
~~~

Checked dependencies:

* continuous_quittingTerminalSemanticPrefix;
* continuous_quittingTerminalOutcomeLawPrefix;
* quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash;
* literal stage-mass scaling under common prefixes;
* literal payoff-difference scaling under common prefixes;
* compactness of the semantic and joint semantic/law carriers; and
* the pure-pair tail-independence and exact own-debt subtraction results.

## 11. Verdict

The invariant-density infimum argument succeeds, but only on the correct
augmented state:

\[
\boxed{
\begin{array}{c}
\text{compact closure of source-attached marked-pair prefix descendants}\\
+\ \text{fixed pair-mass/debt and paid-gain/debt floors}\\
\Downarrow\\
\text{minimum return}
\quad\lor\quad
\text{unique all-Continue exact root}.
\end{array}}
\]

There is no infinite support-entry descent and no degradation of normalized
thresholds. The remaining forced-pair obstruction is purely the inert
normalized-passport minimizer.
