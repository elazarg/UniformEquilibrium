# Screened-hard rational negative search

**Identity:** `CODEX_DESCENDANT`  
**Status:** exact finite filters plus bounded experiment; no counterexample and
no all-behavior lower certificate

## Question

Can one exhibit a rational four-player quitting table which simultaneously

1. lies in the screened-hard table normal form;
2. has no exact equilibrium in any of the three complementary-pair period-two
   classes, including their vanishing-hazard boundaries; and
3. survives the currently implemented stationary and finite-period upper
   witnesses,

and then upgrade it to an escape-aware all-behavior positive-gap certificate?

A numerical gap in a bounded profile class is not a valid output.  A table is
a serious negative candidate only after exact exclusion of the finite classes
and production of the lower certificate required by the existing exact
semidecision hierarchy.

## 1. Exact rational screens used

For a rational table, T1, T3, T4, and T5 of the screened-hard normal form are
finite rational sign tests.  I also used the following exact linear-program
test for T6.

For every unordered pair (p\ne q), maximize (z) subject to

\[
 \theta_i\ge0,\qquad \sum_i\theta_i=1,\qquad
 \theta\cdot s\ge0,
\]

\[
 \theta\cdot(r(S)-s)\le0\quad(S\ne\varnothing),
 \qquad \theta_p\ge z,\quad\theta_q\ge z.
\]

There exists a forbidden social costate with at least two positive
coordinates if and only if one of these six exact rational programs has
optimum (z>0).  This avoids replacing “at least two positive” by a closed
but inequivalent support condition.

For the matrix part of T2, the main scan fixed the already checked matrix

\[
 M=\begin{pmatrix}
 0&3&-1&-1\\
 3&0&-1&-1\\
 -1&-1&0&3\\
 -1&-1&3&0
 \end{pmatrix}.
\]

The repository proves that this matrix has full normal core, is standard-Q,
has no homogeneous simplex solution, and is not projective-
\(\overline Q\).  Its row sums are all one.  Hence the uniform mass vector
has full support and its singleton mixture is strictly above the solo target
in every coordinate.  Full normality gives punishment normality, so
`normalFullSupportSingletonPacket` supplies the remaining packet field in T2.
I selected solo values (s_i\in\{-2,-1,0,1,2\}), set

\[
 r_i(\{j\})=s_i+M_{ij},
\]

and sampled all nonsingleton reward coordinates from
(\{-4,-3,\ldots,4\}\).  Thus the search did not infer the hard matrix
properties from a floating-point LCP heuristic.  Full normality follows from
the checked normal-core-to-punishment-normal implication.

## 2. Complementary-pair escape screen

For a fixed complementary partition, positive-scale exact Nash is a compact
rational semialgebraic feasibility problem in four hazards.  The separately
proved escape-aware boundary reduction says that, because this (M) has no
homogeneous simplex solution, a sequence in the class cannot have both
exploitability tending to zero and all hazards tending to zero.  Therefore an
exact sign-cover exclusion of the positive-scale system would exclude the
entire approximate class.

During search I used the existing exact periodic best-response evaluator and
floating optimization only as a rejection oracle.  It is not an exact
exclusion certificate.

## 3. Search result

With deterministic seed `0xF104BEEF`, 18,000 fixed-matrix integer tables gave

* 2,572 with no pure product equilibrium among the sixteen pure coalitions;
* 1,568 also satisfying the integer-margin T3 screen;
* 1,566 also satisfying T4; and
* all retained leading candidates passing the exact six-program T6 test.

The leading tables under coarse stationary and complementary-pair rejection
did not survive continuous re-optimization.  Their best displayed bounded
exploitabilities fell to between zero and roughly (3\cdot10^{-3}).

The most instructive leading table had digest
`503ca77d548d2e23`.  A local optimizer reported a complementary-pair gap near
(1.2\cdot10^{-3}) for the partition

\[
 \{0,3\}\mid\{1,2\}.
\]

Solving the four active indifference equations at 85-digit precision instead
gave the interior hazards

\[
 (x_0,x_1,x_2,x_3)\approx
 (0.0992613984,0.0396608181,0.1053636367,0.0333230568).
\]

The four inactive-phase Quit-minus-Continue differences were approximately

\[
 -0.5140,\quad -0.1721,\quad -0.1740,\quad -0.4355.
\]

Thus the apparent gap was numerical optimizer error around a robust interior
complementary-pair Nash point, not evidence for exact exclusion.  This is an
experiment, not an interval proof of existence, but the large strict inactive
margins make the diagnosis unambiguous for search triage.

Conversely, another retained table (`2d455f4d6bb8afc1`) had no Nash point at
the active root found for that same pair schedule: two inactive inequalities
had the wrong sign.  Its stationary optimizer, however, had exploitability
below (10^{-6}), and high-precision continuation of analogous leading
stationary points repeatedly converged to interior indifference roots.

The search therefore encountered the disjunction

\[
 \text{complementary-pair upper witness}
 \quad\text{or}\quad
 \text{stationary/general-periodic upper witness},
\]

not a table outside both.

## 4. What the failure says

The exact table normal form and complementary-pair escape exclusion are not
close to a lower certificate by themselves.  They leave enough nonsingleton
reward freedom for a different small finite timing chamber to open whenever a
selected pair chamber is suppressed.  This is evidence about search
conditioning, not a theorem that the disjunction is exhaustive.

In particular, the following implications remain invalid:

* a positive numerical minimum over the three pair schedules does not prove
  their exact exclusion;
* exact exclusion of all three pair schedules does not give an all-behavior
  positive gap;
* T1--T6 do not preclude stationary or other finite-period equilibria; and
* a small positive optimizer residue is not a candidate certificate.

The precise additional finite task before invoking the all-behavior search is
to produce exact sign-cover certificates for all three pair systems **and**
exactly exclude the stationary active-face systems.  Only then is it useful
to spend exact-certificate effort on escape-aware clocks and longer words.

## 5. Strongest surviving direction

The experiment suggests a finite alternative worth testing as mathematics:

> Under the fixed checked paired singleton matrix, T1, T3, T4, and T6, must a
> table have either a stationary exact Nash point or an exact Nash point in
> one of the three complementary-pair period-two classes?

This statement is not proved and may be false.  It is sharply falsifiable by
the same rational search, and a proof would consume this entire hard-matrix
subfamily rather than merely improve a numerical objective.  A disproof must
come with exact semialgebraic exclusions, not optimized residuals.

## 6. Positive diagonal hard-matrix enlargement

The symmetric fixed matrix is an unnecessarily narrow search family.  Let
(D,E) be positive diagonal rational matrices and put

\[
 M'=DME.
\]

This remains an exact hard singleton matrix.  Indeed, for every right-hand
side (q), a standard LCP solution for (M) at (D^{-1}q) transports by
the positive coordinate change (z'=E^{-1}z); residuals are multiplied by
(D), and each complementarity product is multiplied by a positive scalar.
The inverse transformation gives the converse.  The same change of variables
preserves homogeneous simplex feasibility after renormalizing the positive
weight vector.  Signs, full normal core, and the selected nonprojective
principal are unchanged.

The full-support packet also transports explicitly.  Put

\[
 c=\left(\sum_j E_{jj}^{-1}\right)^{-1},
 \qquad m_j=cE_{jj}^{-1}.
\]

Then \(m\) is a strictly positive probability vector and

\[
 M'm=DME m=cD M\mathbf 1=cD\mathbf 1>0.
\]

Thus the singleton mixture is strictly above the solo target in every
coordinate, and the same normal-packet constructor certifies the full-support
part of T2 throughout this enlarged family.

I therefore repeated the rational search with

\[
 D_{ii},E_{ii}\in\{1,2,3,4\},
\]

random integer solo baselines, and random nonsingleton entries at the induced
reward scale.  This produced a substantially stronger bounded-search
survivor with digest `8033ab74e6deb232`, scales

\[
 \operatorname{diag}D=(2,3,4,3),\qquad
 \operatorname{diag}E=(4,4,4,1),
\]

complementary-pair residue approximately (0.275), stationary-search residue
approximately (0.217), and no exact T6 costate.

The candidate nevertheless failed the broader upper-witness battery.  A
period-one boundary profile with hazards approximately

\[
 (0.4935,0.99998,0.5715,1)
\]

had exploitability below (4\cdot10^{-4}).  Thus the first stationary
optimizer had missed a face with two nearly sure quitters.  The candidate is
rejected.

This failure adds a concrete mandatory screen: exact stationary exclusion
must enumerate all cube faces, including hazards fixed to zero or one.  An
interior sigmoid optimizer is not an adequate rejector even when its reported
gap is macroscopic.  The positive-diagonal family remains the better exact
matrix family for further negative search.  Most retained members fail the
complete finite-period battery.  One bounded-search survivor, digest
`7dc6fad99c6ec955`, has raw battery residue about
\(2.31\mathbin{\cdot}10^{-2}\), but its reward bound is \(37\), so its
scale-normalized residue is only about \(6.25\mathbin{\cdot}10^{-4}\).  It is
not an exact candidate or lower certificate.  This also exposes a defect in
the first ranking: raw, rather than scale-normalized, exploitability favored
large diagonal scalings.  Any further search intended to feed the exact
semidecision must rank the ratio of the observed gap to the reward bound.

## 7. Scale-normalized separation is the only certificate-relevant score

For every positive scalar \(c\) and every behavioral profile \(\sigma\),

\[
 U_i^{cr}(\sigma)=cU_i^r(\sigma),\qquad
 B_i^{cr}(\sigma)=cB_i^r(\sigma).
\]

Therefore

\[
 \operatorname{Expl}_{cr}(\sigma)=c\operatorname{Expl}_r(\sigma),
 \qquad
 \eta(cr)=c\eta(r).
\]

It follows that the dimensionless ratio

\[
 \frac{\eta(r)}{\lVert r\rVert_\infty}
\]

is invariant under positive rescaling.  The same holds for every bounded
profile-class upper witness computed by the battery.  Since the exact search
normalizes the table before choosing its finite-clock scale, a raw numerical
gap has no certificate significance independently of the reward bound.  This
is an exact correction to the candidate-generation objective, not an
additional upper-witness theorem.

I reran the diagonal-family screen with this corrected objective.  Among
25,000 rational tables, the best four after complementary-pair and stationary
optimization had dimensionless two-class residues approximately

\[
 3.18\mathbin{\cdot}10^{-3},\quad
 2.48\mathbin{\cdot}10^{-3},\quad
 1.11\mathbin{\cdot}10^{-3},\quad
 2.74\mathbin{\cdot}10^{-4}.
\]

The broader periodic battery reduced the first three to, respectively,

\[
 5.52\mathbin{\cdot}10^{-5},\quad
 2.17\mathbin{\cdot}10^{-6},\quad
 6.47\mathbin{\cdot}10^{-7},
\]

through general-periodic upper witnesses.  The fourth remained at
\(2.74\mathbin{\cdot}10^{-4}\), bound by a stationary witness.  Thus the
scale correction does not presently produce a table close to the practical
input range of the exact resolver.  The experiment again suggests that
general-periodic and boundary stationary faces, rather than the three
complementary-pair classes, are the dominant upper witnesses in this family.

## 8. Exact elimination of the sole bounded survivor

The earlier sole bounded-battery survivor `7dc6fad99c6ec955` is not a
counterexample.  A deeper boundary attack suggested the exact hazards

\[
 q=(0,17/18,14/17,1).
\]

The underlying integer reward table, in coalition-mask order, is

\[
\begin{array}{c|rrrr}
S& r_0(S)&r_1(S)&r_2(S)&r_3(S)\\ \hline
\{0\}&3&24&-11&-18\\
\{1\}&30&0&-8&-14\\
\{0,1\}&-12&-5&-24&1\\
\{2\}&0&-2&1&10\\
\{0,2\}&-34&-35&14&30\\
\{1,2\}&-3&21&-32&-27\\
\{0,1,2\}&-16&13&37&9\\
\{3\}&-9&-8&37&-2\\
\{0,3\}&34&23&-20&-6\\
\{1,3\}&33&34&30&34\\
\{0,1,3\}&-23&25&-35&26\\
\{2,3\}&-8&33&3&-3\\
\{0,2,3\}&26&19&-26&-8\\
\{1,2,3\}&31&24&32&17\\
I&2&19&12&11
\end{array}
\]

Because player 3 Quits surely, prescribed play absorbs at date zero.  Exact
rational evaluation gives

\[
 U=(1487/51,438/17,547/18,2866/153).
\]

Against stationary opponents, a pure stopping time has value between the
Quit-now and Never values: before its stopping date it receives the same
opponent-absorption payoff as Never, and conditional on reaching that date
the stationary opponent law restarts.  Hence the unrestricted behavioral cap
is the maximum of those two extreme values.  Here they are

\[
\begin{array}{c|cc|c}
i&Q_i&N_i&\max(Q_i,N_i)-U_i\\ \hline
0&-77/102&1487/51&0\\
1&438/17&438/17&0\\
2&547/18&547/18&0\\
3&2866/153&-7000/303&0.
\end{array}
\]

Thus \(q\) is an exact one-root terminal Nash profile, with complete
behavioral caps, and supplies an exact uniform-equilibrium payoff for this
table.  The apparent dimensionless battery gap
\(6.25\mathbin{\cdot}10^{-4}\) was entirely a boundary-optimizer failure.
After this exact elimination, the diagonal hard family contains no surviving
candidate from the present scan.

## Inspected sources

* `CODEX_TABLE_NORMAL__FIN4_COUNTEREXAMPLE_ONE_WAY_REWARD_NORMAL_FORM.md`;
* `CODEX_DESCENDANT__ESCAPE_AWARE_COMPLEMENTARY_PAIR_EXCLUSION.md`;
* `singleton_collision_candidate_search.py`;
* `certsearch/filters.py`, especially exact singleton-LCP support
  enumeration; and
* the checked paired-singleton matrix declarations used by
  `BallisticNormalizedSelectedChainRegression.lean` and
  `FourPlayerPairedSingletonResidualHard.lean`.
