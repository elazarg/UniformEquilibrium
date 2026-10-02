# Capacity-gap root matching or a persistent inner charged mark

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; source-marked reduction, not Lean-checked and
not a complete consumer.** A capacity-near exact root on the high side of a
vanishing payoff seam either remains a fixed distance from every low-side
exact root, or it has an exact low-side mate. In the matched case, the
canonical capacity gap transfers to the two common successors.

Starting from the reviewed renewed-source singleton wall, the first
high-side root has a fixed positive absorption floor. Iterating the matching
alternative retains that first root as an inner literal mark in every finite
exact predecessor word. Bounded exact capacity makes all later outer charges
summable. Unless a later limiting root has sure absorption, the inner charged
mark retains positive projective reach while escaping to infinity. One fixed
terminal coalition, and every one of its members' finite stopping clocks,
then carry a uniform mass floor at the escaping date. Thus the actual finite
words have no strategically total-variation-compact cofinal subsequence.

This gives a precise source-marked all-summable predecessor object. It does
not actualize the infinite outward word as one behavioral profile.

## 1. One-step root matching

Let \(\phi\) be the bounded canonical full-box exact predecessor capacity.
Let \(u_n,v_n\) be payoff sequences in that fixed compact box such that

\[
 u_n-v_n\longrightarrow0,\qquad
 \phi(u_n)-\phi(v_n)\ge\kappa>0.
\tag{1}
\]

Choose \(\varepsilon_n\downarrow0\). Since
\(\phi(u_n)\ge\kappa\), choose a nonempty finite exact path from \(u_n\)
whose charge is at least \(\phi(u_n)-\varepsilon_n\). Let \(q_n\) be its
first exact root and set

\[
 u'_n=F(q_n,u_n).
\tag{2}
\]

Write \(\mathcal R(v)\) for the nonempty compact set of exact roots against
\(v\), and put

\[
 \rho_n=\operatorname{dist}(q_n,\mathcal R(v_n)).
\tag{3}
\]

### Theorem 1.1: separation or exact matching

After first passing to a subsequence with
\(u_n,v_n\to u_*\), exactly one of the following alternatives holds.

1. **Separated limiting roots.** There are \(q^+,q^-\in\mathcal R(u_*)\)
   and \(\rho>0\), where \(u_n,v_n\to u_*\), such that

   \[
   q_n\to q^+,\qquad
   r_n\to q^-\text{ for some }r_n\in\mathcal R(v_n),
   \qquad
   \lVert q^+-q^-\rVert_\infty\ge\rho.
   \tag{4}
   \]

2. **Matched successor shift.** There are
   \(r_n\in\mathcal R(v_n)\) with

   \[
   \lVert q_n-r_n\rVert_\infty\longrightarrow0.
   \tag{5}
   \]

   Putting \(v'_n=F(r_n,v_n)\), one has

   \[
   u'_n-v'_n\longrightarrow0,\qquad
   \phi(u'_n)-\phi(v'_n)\ge\kappa-o(1).
   \tag{6}
   \]

#### Proof

Compactness of the payoff box and \(u_n-v_n\to0\) give the asserted common
payoff limit after a subsequence. Compactify \(q_n\). If \(\rho_n\) has a
positive lower bound along a
subsequence, choose arbitrary \(r_n\in\mathcal R(v_n)\) and compactify those
roots too. Closedness of the exact-root graph places both limits in
\(\mathcal R(u_*)\), while (3) keeps them separated. This proves (4).

Otherwise pass to a subsequence with \(\rho_n\to0\) and choose \(r_n\) within
\(o(1)\) of the distance. Bellman continuity gives the first part of (6).
The suffix of the nearly maximizing high path gives

\[
 \phi(u'_n)\ge
 \phi(u_n)-\operatorname{Abs}(q_n)-\varepsilon_n,
\tag{7}
\]

while prepending \(r_n\) to paths from \(v'_n\) gives

\[
 \phi(v_n)\ge
 \operatorname{Abs}(r_n)+\phi(v'_n).
\tag{8}
\]

Subtract and use (1), (5), and continuity of absorption. QED

No uniqueness assumption is used. Singletonness of the limiting root set is
a sufficient condition forcing alternative 2, but exact matching is the
strictly weaker property needed by the capacity calculation.

## 2. Quantitative first fork at the renewed singleton wall

Now let

\[
 X_n=(u_n,B_n),\qquad Y_n=(v_n,C_n)
\tag{9}
\]

be the high reset child and low exact-prefix sibling in the small full
terminal-semantic seam of the renewed Fin4 capacity ledger. The transferred
singleton-wall theorem supplies constants \(\alpha,\Delta>0\) such that
every sufficiently late exact root on both sides:

- has absorption at least \(\alpha\); and
- when prefixed to its corresponding complete semantic pair, spends at
  least \(\Delta\) of the named and total semantic debt.

Therefore, if Theorem 1.1 stops in alternative 1 at the first level, both
limiting roots in (4) satisfy

\[
 \operatorname{Abs}(q^+),\operatorname{Abs}(q^-)\ge\alpha.
\tag{10}
\]

This is not merely an abstract multi-root payoff. The high roots are first
rows of capacity-near exact paths at actual reset-child payoff sources, and
the low roots arise at the vanishing-seam actual prefix siblings.

If alternative 2 holds, both first prefixes are literal exact prefixes, stay
semantically \(o(1)\)-close, have charge at least \(\alpha\), and spend at
least \(\Delta\) of debt. Their successor payoffs retain the capacity gap.

## 3. Iterated matching preserves a literal inner mark

Apply Theorem 1.1 repeatedly to the successor sequences whenever the matched
alternative holds. At step \(k\), spend an error at most
\(\kappa/2^{k+2}\), so the capacity gap remains at least \(\kappa/2\) at
every finite depth.

For each depth \(K\), the high construction is one literal exact predecessor
word

\[
 q_{n,K-1}\triangleright\cdots\triangleright q_{n,1}
 \triangleright q_{n,0}\triangleright X_n.
\tag{11}
\]

The root \(q_{n,0}\) is the original marked first root and

\[
 \operatorname{Abs}(q_{n,0})\ge\alpha.
\tag{12}
\]

All roots outside it were selected as exact first roots at the literal
successive predecessor payoffs; separately selected sibling rows are not
being concatenated.

If root separation occurs at some later finite depth, (11) retains the
entire earlier exact ancestry and the inner mark (12). The separated limiting
roots at that later depth need not themselves inherit the first singleton
wall.

If matching continues at every depth, diagonal compactness gives an infinite
outward exact predecessor spine

\[
 u^{k+1}_*=F(q^k_*,u^k_*),\qquad k\ge0,
\tag{13}
\]

with

\[
 \operatorname{Abs}(q^0_*)\ge\alpha.
\tag{14}
\]

Every finite initial segment is a canonical exact path. The checked bounded
Fin4 exact-block capacity therefore gives

\[
 \sum_{k\ge0}a_k<\infty,\qquad
 a_k:=\operatorname{Abs}(q^k_*).
\tag{15}
\]

## 4. Sure screen or positive projective reach

Before reading the outward word, two limiting root geometries are already
terminal consumers.

### Proposition 4.1: terminal high-lift screens

Let \(Z_n=(u_n,B_n)\to Z_*=(u_*,B_*)\) be actual semantic pairs, let
\(q_n\) be exact roots against \(u_n\), and suppose \(q_n\to q_*\).
The literal prefixes \(q_n\triangleright Z_n\) are terminal approximate Nash
profiles if either:

1. \(q_*\) has two distinct sure quitters; or
2. for one player \(j\), \(q_*\) is the pure singleton-\(j\) root and
   \(B_{*,j}=r_j(\{j\})\).

Their payoffs converge to the fixed Bellman vector \(F(q_*,u_*)\). Hence
either case produces a uniform-equilibrium payoff by fixed-target terminal
acceptance.

For case 1, every player has a sure quitter among its opponents, so its
opponent-Continue factor tends to zero. The exact semantic-prefix debt
formula bounds its new debt by that factor times the bounded tail debt.

For case 2, the same argument kills every outsider debt. For \(j\), at the
limit the opponents' Continue factor is one, while the exact exercise
premium is

\[
 r_j(\{j\})-u_{*,j}=B_{*,j}-u_{*,j}.
\tag{16}
\]

Thus the positive-part debt action kills \(j\)'s entire tail debt. Continuity
of the finite semantic prefix map makes all four debts of the actual finite
prefixes tend to zero. Bellman continuity gives the asserted fixed payoff.

In the maintained no-uniform-payoff wall, every high- or low-side limiting
root has actual exact lifts and \(B_{*,j}=r_j(\{j\})\). Therefore neither a
two-sure root nor the pure singleton root of the pinned player can occur in
the surviving first multi-root alternative.

The chronological finite word corresponding to the first \(K\) predecessor
steps is read in reverse order:

\[
 q^{K-1}_*,\ldots,q^1_*,q^0_*,
\tag{17}
\]

over the original tail payoff. The probability of reaching the inner mark
\(q^0_*\) is

\[
 R_K=\prod_{k=1}^{K-1}(1-a_k).
\tag{18}
\]

There are two exact cases.

1. If some \(a_k=1\) for \(k\ge1\), a finite outer root surely absorbs and
   screens the inner mark. Proposition 4.1 consumes a two-sure limit. If it
   has a unique sure quitter, the screen fails exactly for that quitter: its
   deviation can delete the only sure hazard and expose the continuation cap.
   This is the unique-sure limiting handoff boundary; no finite exact sure
   root is inferred.
2. If every \(a_k<1\), (15) implies

   \[
   R_\infty:=\prod_{k\ge1}(1-a_k)>0.
\tag{19}
   \]

   Hence the inner marked root retains limiting reached absorption mass

   \[
   R_\infty\operatorname{Abs}(q^0_*)\ge R_\infty\alpha>0.
\tag{20}
   \]

Equation (20) is the precise persistent-inner-mark output. It does not
define an infinite behavioral word: as \(K\to\infty\), the marked row moves
to date \(K-1\). Every fixed initial time window instead converges to all
Continue.

### Corollary 4.2: one fixed terminal coalition survives

For Fin4, the nonempty coalition masses at \(q^0_*\) sum to at least
\(\alpha\). Hence one fixed nonempty coalition \(A_*\) satisfies

\[
 \Pr_{q^0_*}(A_*\text{ is the quitting coalition})\ge\alpha/15.
\tag{21}
\]

In alternative 2 above, the terminal probability that the finite reversed
word reaches the inner row and then absorbs at \(A_*\) converges to at least

\[
 R_\infty\alpha/15>0.
\tag{22}
\]

More explicitly, at depth \(K\) choose the original source index \(n(K)\)
so large that all of the first \(K\) actual roots are close enough to their
limiting roots for the corresponding finite product and the inner coalition
mass to differ by at most \(o_K(1)\). Since the limiting product is \(R_K\)
and \(R_K\to R_\infty\), the literal finite words over the actual high
sources therefore carry the same coalition
label \(A_*\), at their moving inner date, with a common positive terminal
mass floor such as \(R_\infty\alpha/30\). This is a genuine terminal-law
mark, not merely a scalar absorption annotation.

### Corollary 4.3: exact strategic noncompactness

Let \(i\in A_*\). Along the diagonal literal actual words, for every fixed
finite cutoff \(T\),

\[
 \liminf_K
 \Pr(T_i>T,\ T_i<\infty)
 \ge R_\infty\alpha/30.
\tag{23}
\]

Consequently these marginals have no total-variation-convergent cofinal
subsequence and no common finite-tail tightness envelope.

Indeed, the event from Corollary 4.2 makes player \(i\) Quit at the moving
inner date, which eventually lies after \(T\). This proves (23). If a
cofinal subsequence converged in total variation to one actual stopping law
\(\nu\), then for every fixed \(T\) its mass on
\(\{T+1,T+2,\ldots\}\) would inherit the same lower bound. Letting
\(T\to\infty\) contradicts countable additivity of the finite part of
\(\nu\). Notice that no assumption on the Never mass of the actual tails is
needed.

This is the same strategic topology obstruction as the checked positive-
minimum exact-prefix clock-escape theorem, now derived from capacity-root
matching and a retained inner root. That theorem is a no-go, not a terminal
consumer. Its fixed-tail theorem cannot simply be invoked here: the actual
high tails and every finite outer root word are selected diagonally with the
depth. The varying-tail statement proves the same clock escape once the
moving mark is supplied, but does not reconstruct a common terminal payoff
or cap.

## 5. Exact residual

The small-seam fixed-capacity-recharge branch now has the following exhaustive
finite-dimensional/projective split.

1. A capacity-selected high root is separated from every low-side exact root.
   At the first level this gives two distinct positive roots with the common
   quantitative wall.
2. The root has exact low-side mates for finitely many levels and then a
   separated root fork appears, retaining a finite literal exact ancestry and
   the original inner charged mark.
3. Matching continues forever and a later sure root screens the mark.
4. Matching continues forever without a sure outer root, and the original
   charged mark, including one fixed nonempty terminal coalition, survives
   at positive projective reach while escaping every fixed clock window. Its
   coalition members' stopping laws fail total-variation compactness by
   (23).

Alternatives 2--4 contain more ancestry than a bare all-summable capacity
path. They still do not provide an endpoint payoff return or actual
infinite-profile limit.

## Checked sources inspected

- CODEX_SPINOZA__TWO_SIDED_SINGLETON_WALL_UNIQUE_ROOT_CAPACITY_SHIFT, frozen
  at SHA-256
  43d71ec684bb8e014c0114f988d2fe253aeea6f1b6c40136b08eb88fce160d81;
- CODEX_HAHN__RENEWED_SOURCE_FLOOR_ELIMINATES_DELAYED_CAPACITY_ESCAPE,
  reviewed at SHA-256
  279feaea606e31690e7c5115b5d42b000a14a97e3ba30ac24d42093b226cf7e4;
- CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE;
- CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER;
- isClosed_isZeroQuittingRootEndpointNash_simplex in
  UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean; and
- finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff
  in
  UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean;
- POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE, for the checked distinction
  between moving finite clock mass and an executable stopping-law limit; and
- CODEX_SOURCE_GATE__OFFMINIMUM_POSITIVE_ROOT_ZENO_FACE_SATURATION, for the
  exact outward/chronological orientation and upstream-mark boundary.

## Boundary and nonclaims

- The root metric can be any fixed compatible metric on the finite product
  simplex. No uniform game-level lower bound on the separation \(\rho\) is
  claimed.
- Later root forks do not inherit the singleton wall unless an additional cap
  pin is propagated.
- A limiting sure root need not be exactly sure at any finite actual source.
  Only the two-sure limiting screen has the stated terminal approximation.
- Positive projective reach in (19) is a limit of finite-word reach
  probabilities, not a new date after all natural-number prefixes.
- The persistent inner mark is an exact absorbing root at a limiting payoff.
  It is approached by literal marked rows at actual finite sources, but it is
  not itself asserted to be realized at one fixed behavioral source.
- Corollary 4.3 is a compactness obstruction. The maintained two-cut source
  adapter requires a minimum-source semantic/law limit, while these reversed
  finite words lose precisely the strategic stopping-law compactness needed
  to provide one. The tangent-frontier paid-row theorem likewise applies to
  its supplied full-replacement source family, not to this diagonally chosen
  predecessor family.
- No floor-admissible payoff return, renewable rank, terminal equilibrium in
  the unique-sure arm, or uniform-equilibrium payoff is proved.

## Next exact question

At the first separated multi-root face, does Fin4 complementarity plus the
named singleton wall force a two-sure root or a literal common-tail edge?
Absent such a theorem, the infinite matched branch has reached the sharp
known clock-escape boundary: a fixed terminal absorption atom escapes to
infinity while no source-compatible payoff/cap continuation survives.
