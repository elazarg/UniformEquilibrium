# Actual Zeno descendants split into host compression or full screening

Author: CODEX_AMPERE

Independent reviews:

- [CODEX_CURIE](../feedback/CODEX_AMPERE__ACTUAL_ZENO_DELETED_SURVIVAL_PASSPORT__BY_CODEX_CURIE.md)
- [CODEX_ROOT](../feedback/CODEX_AMPERE__ACTUAL_ZENO_DELETED_SURVIVAL_PASSPORT__BY_CODEX_ROOT.md)

The actual source-level host-or-screening contraction is checked in Lean.
`FinFourNormalizedInertVanishingDensityBoundary.nonempty_actualZeno_fixedEndpoint_or_coalescingClearingFamily`
in
`Research/Quitting/FinFourProducerAtlas/ActualZenoFullyScreenedSiblingCoalescence.lean`
constructs one literal Zeno source from the zero-mass normalized boundary.
It returns either a fixed positive-host endpoint sequence, with the original
packet/source ranks, positive marked-mass floor, zero marked-host root defect,
unchanged nonhost behaviors, and complete postmark spine, or the existing
fully screened finite-clearing family together with the full-screening proof
for that same source.  The latter proof gives coordinatewise convergence of
the original siblings' complete prescribed payoffs, unrestricted behavioral
caps, and terminal laws, and the clearing family has the checked strategic-
singleton-or-collision-minimum consumer.

The packet is not fully formalized as written only because the explicit
reward-table regression with `H_i = n^-3`, positive marked tail debt, unique
all-Continue limiting cap root, and global minimum zero is not formalized.
The integrated contraction has `M`, `L`, and `A` in both arms, with `C` only
on the fully screened clearing arm; the positive-host endpoint is not
whole-profile near-minimal, cross-cap coherent, or cap controlled in its other
coordinates, and has no consumer.  Revisit this packet when the boundary
regression is checked or the positive-host endpoint gains a genuine downstream
consumer.

## Exact statement

Let \(I=\operatorname{Fin}4\). Consider a sequence of literal finite premark
product-root words followed by one fixed pure marked pair and an arbitrary
bounded behavioral tail. For word \(n\), let

\[
S_{i,n}:=\Pr(i\text{ Continues at every premark root}),
\]

let

\[
M_n:=\prod_{i\in I}S_{i,n}
\]

be the unconditional mass of the marked pair, and let

\[
H_{i,n}:=\prod_{k\ne i}S_{k,n}
\]

be the probability that all opponents of player \(i\) survive to the mark.
Assume \(M_n\to0\). After passage to a subsequence, exactly one of the
following alternatives holds.

1. **One-host compression.** There are a fixed player \(h\) and \(\eta>0\)
   such that \(H_{h,n}\ge\eta\) for every retained \(n\), while
   \(H_{i,n}\to0\) for every \(i\ne h\). By modifying only \(h\)'s actions
   before and at the marked row, one obtains actual source-attached profiles
   whose marked nonempty coalition has mass at least \(\eta\), whose marked
   \(h\)-coordinate Nash defect is zero, and whose complete postmark
   behavioral tail is literally unchanged. After a further finite-label
   subsequence, the selected Boolean endpoint and marked coalition are fixed.

2. **Full screening.** For every player \(i\), \(H_{i,n}\to0\). If two
   source siblings have the same premark word and tail and differ only in one
   player's Boolean action at the marked row, then their complete prescribed
   payoff vectors, unrestricted behavioral best-response cap vectors, and
   terminal laws coalesce.

The full-screening alternative cannot be excluded using only product
realizability, a fixed paid pair label, a fixed positive-debt common tail,
whole-law provenance, or uniqueness of all-Continue at the limiting cap.
There is an explicit four-player reward table and actual prefix sequence with
all of those properties. Its global minimum debt is zero. Thus positive
global-minimum provenance is an essential additional input to any consumer of
the full-screening arm.

## Conjecture-facing change

The normalized inert Zeno boundary previously retained only a scalar marked
mass tending to zero. This theorem adds the actual deleted-survival passport

\[
(H_0,H_1,H_2,H_3)
\]

and strictly contracts the actual realizability problem to

\[
\boxed{
\text{source-attached concentrated endpoint}
\quad\lor\quad
\text{fully screened positive-minimum prefix escape}.}
\]

The positive-coordinate arm is an executable producer, not a supplied-object
test. The all-zero arm is a precise remaining obligation. The regression
proves that no argument which ignores positive global-minimum provenance can
eliminate it.

## Definitions and probability mode

Before absorption, a quitting game has one public live history at each date.
At each root, players independently choose Quit or Continue according to the
prescribed behavioral profile. The finite premark word includes every root
strictly before the marked row, including both newly prefixed roots and roots
of the originating actual profile.

The cap \(B_i\) is the supremum over all unilateral behavioral strategies of
player \(i\). It includes Never, arbitrarily late deterministic quitting,
calendar-dependent hazards, and private randomization. No stationary or
bounded-controller restriction is imposed.

Two marked siblings share the whole premark word, every opponent strategy of
the marked mover, and the complete postmark tail. They differ only in that
mover's Boolean action at the marked row.

## Source correspondence

The source is the actual raw-descendant side of the normalized passport orbit
in:

- Research/Quitting/NormalizedPassportPrefixOrbit.lean;
- Research/Quitting/NormalizedPassportMinimizer.lean;
- Research/Quitting/NormalizedPassportMinimumReturn.lean;
- Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean; and
- Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean;
- Research/Quitting/FinFourProducerAtlas/ActualZenoHostCompression.lean; and
- Research/Quitting/FinFourProducerAtlas/ActualZenoFullyScreenedSiblingCoalescence.lean.

The common-prefix cap mechanism is related to
UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean and
UniformEquilibrium/Quitting/Root/TerminalDebtGreenAccount.lean. The new
content is the exact finite-word inequality \(H_iH_j\le M\), its exhaustive
one-host/full-screening consequence, the literal host-compression producer,
the all-behavior cap-coalescence estimate, and the exact zero-minimum
regression.

No paper theorem is used.

## Proof

### 1. Pairwise deleted-survival inequality

Independence across players gives

\[
M_n=\prod_{i\in I}S_{i,n},
\qquad
H_{i,n}=\prod_{k\ne i}S_{k,n}.
\]

For distinct \(i,j\),

\[
\begin{aligned}
H_{i,n}H_{j,n}
 &=\left(\prod_{k\ne i}S_{k,n}\right)
   \left(\prod_{k\ne j}S_{k,n}\right)\\
 &=M_n\prod_{k\ne i,j}S_{k,n}\\
 &\le M_n.
\end{aligned}
\tag{1}
\]

This proof uses no division and remains valid when a survival factor is zero.
When \(H_{i,n}>0\), it also gives

\[
S_{i,n}=\frac{M_n}{H_{i,n}}.
\tag{2}
\]

### 2. Exhaustive subsequence split

The vector \((H_{i,n})_{i\in I}\) lies in the compact cube \([0,1]^4\).
Take a convergent subsequence with limit \((h_i)_i\). Since \(M_n\to0\),
equation (1) implies

\[
h_ih_j=0\qquad(i\ne j).
\]

Thus at most one limiting coordinate is positive. If none is positive, all
deleted reaches tend to zero. Otherwise, after discarding finitely many
terms, one fixed \(h\) and one \(\eta>0\) satisfy

\[
H_{h,n}\ge\eta.
\]

For \(i\ne h\), equation (1) yields

\[
H_{i,n}\le \frac{M_n}{H_{h,n}}
          \le \frac{M_n}{\eta}\longrightarrow0,
\]

and equation (2) gives \(S_{h,n}\to0\). This proves the dichotomy.

If the normalized carrier points are limits rather than literal profiles,
choose a raw decoration near the \(n\)-th carrier point with positive marked
mass and error less than

\[
\min\{1/n,M_n/2\}.
\]

This diagonal raw sequence still has positive mass tending to zero, so the
same compact subsequence argument applies to literal source descendants.

### 3. Host compression

Let \(C\) be the pure marked pair and \(\tau\) its literal postmark tail. In
the one-host arm:

- keep every opponent of \(h\) unchanged through the premark word;
- force \(h\) to Continue through that word;
- at the mark, choose whichever of \(h\)'s two Boolean endpoints maximizes
  \(h\)'s payoff against the actual marked opponents and tail; and
- leave every root strictly after the mark unchanged.

The modified profile reaches the mark with probability exactly \(H_h\). Its
marked coalition is one of

\[
C,\qquad C\setminus\{h\},\qquad C\cup\{h\}.
\]

Because \(|C|=2\), this coalition is nonempty. Its unconditional marked mass
is therefore at least \(\eta\). The chosen endpoint has marked
\(h\)-coordinate defect zero by definition. The postmark profile, semantic
tail, and full tail law are unchanged literally. The original source word,
labels, and chronology remain attached as provenance. There are only two
Boolean choices, so a further subsequence fixes the selected endpoint and
terminal label.

### 4. Full-screening cap coupling

Let \(T_n,S_n\) be target and comparison siblings whose marked mover is \(o\).
Suppose rewards have absolute value at most \(R\). Their prescribed payoff
difference is supported only on the marked event:

\[
U_i(T_n)-U_i(S_n)
 =M_n\bigl(r_i(C)-r_i(C\setminus\{o\})\bigr).
\tag{3}
\]

Their terminal-law total-variation distance is \(M_n\).

For \(i=o\), the opponents are identical, so own-strategy invariance gives

\[
B_o(T_n)=B_o(S_n).
\tag{4}
\]

For \(i\ne o\), fix an arbitrary complete behavioral deviation by \(i\) and
couple the two opponent profiles. They can differ from the deviator's point
of view only if all opponents of \(i\) survive through the premark word. That
event has probability \(H_{i,n}\), and the payoff difference on it is at most
\(2R\). Therefore every deviation payoff differs by at most \(2RH_{i,n}\).
Using

\[
|\sup f-\sup g|\le\sup|f-g|
\]

over the full behavioral strategy space gives

\[
|B_i(T_n)-B_i(S_n)|\le2RH_{i,n}.
\tag{5}
\]

Equations (3)--(5) prove coalescence of prescribed payoffs, unrestricted caps,
and laws in the fully screened arm. Never and arbitrarily late stopping are
included; no best-response attainment is used.

## Boundary regression

Let the players be \(0,1,2,3\). For every nonempty coalition \(A\), define

\[
r_i(A)=
\begin{cases}
-1,&i\in A,\\
0,&i\notin A,
\end{cases}
\]

except

\[
r_1(\{0,1\})=1.
\tag{6}
\]

At a remote marked row let the comparison coalition be \(\{0\}\), the target
coalition be \(\{0,1\}\), and attach to both the same postmark tail consisting
of the pure singleton \(\{0\}\). This tail has total debt \(2\): player \(0\)
can Continue instead of receiving \(-1\), and player \(1\) can join to receive
\(1\).

For \(n\ge2\), put \(\varepsilon_n=1/n\). Prefix both profiles by a common
length-\(n\) word in which every player independently has stopping law

\[
\Pr(T_i=t)=p_n:=\frac{1-\varepsilon_n}{n}
\quad(0\le t<n),
\qquad
\Pr(T_i\ge n)=\varepsilon_n.
\tag{7}
\]

These stopping laws have a standard behavioral-hazard realization. The remote
marked mass and deleted reaches are

\[
M_n=\varepsilon_n^4=n^{-4},
\qquad
H_{i,n}=\varepsilon_n^3=n^{-3}.
\tag{8}
\]

Hence the sequence is fully screened. Player \(1\)'s actual
target-minus-comparison gain is exactly \(M_n\), and its target marked defect
is zero.

A nonsingleton premark outcome requires a finite tie. The union bound gives

\[
\Pr(\text{some finite tie})
 \le {4\choose2}\sum_{t<n}p_n^2
 =6np_n^2
 \le\frac6n.
\tag{9}
\]

The remote mass also vanishes. By symmetry, both terminal laws converge to the
uniform law on the four singleton coalitions, and both prescribed payoff
vectors converge to

\[
(-1/4,-1/4,-1/4,-1/4).
\]

For \(i\ne1\), Never pays zero and every event on which \(i\) quits pays
\(-1\), so \(B_i=0\) exactly. For player \(1\), positive payoff at a premark
pure quitting date requires collision with player \(0\), of probability at
most \(p_n\); at the mark it is bounded by \(n^{-3}\); later quitting is
preempted by player \(0\). Every behavioral strategy is a mixture over its
complete stopping time and Never along the unique live history, hence

\[
0\le B_1\le\max\{p_n,n^{-3}\}\le1/n.
\tag{10}
\]

Thus both semantic pairs converge to

\[
\left((-1/4,-1/4,-1/4,-1/4),(0,0,0,0)\right),
\]

of total debt \(1\). At cap zero, players \(0,2,3\) strictly prefer Continue;
after they Continue surely, player \(1\) receives \(-1\) by quitting alone and
zero by Continuing. Hence all-Continue is the unique exact cap--Nash root.

Nevertheless, all-Never is an exact terminal Nash profile, so the global
minimum debt is \(D_*=0\). This proves the claimed sharpness: every listed
field except positive global-minimum provenance can coexist with full
screening.

## Adapter and consumer

For a literal normalized-passport raw descendant, concatenate every root
strictly before the marked pair and compute the finite products \(S_i,H_i\).
Equation (1) gives the exhaustive adapter.

- A positive limiting \(H_h\) is consumed immediately by the literal host
  modification into a fixed-resolution concentrated endpoint with zero local
  \(h\)-defect and exact tail preservation.
- If every \(H_i\to0\), the old paid sibling is semantically invisible by
  equations (3)--(5). The remaining consumer must use the positive global
  minimum quantitatively to produce a source-faithful earlier return, a
  renewable finite-rank regeneration, terminal approximants, or a
  contradiction.

The theorem deliberately does not claim that host compression preserves
whole-profile near-minimality or prevents cap leakage in the other three
coordinates.

## Lean status

The checked split and host producer are
`FinFourActualZenoDeletedSurvivalSource.nonempty_positiveHost_or_fullyScreened`
and `FinFourActualZenoPositiveHost.nonempty_fixedEndpoint` in
`Research/Quitting/FinFourProducerAtlas/ActualZenoHostCompression.lean`.
The exact screened common-prefix bounds are
`abs_sibling_terminalPayoff_sub_le`,
`abs_sibling_bestResponseValue_sub_le`, and
`abs_sibling_terminalOutcomeMass_sub_le`.  The one-shot source capstone is
`FinFourNormalizedInertVanishingDensityBoundary.nonempty_actualZeno_fixedEndpoint_or_coalescingClearingFamily`.
It retains the full-screening proof and clearing family together, so
`FinFourActualZenoDeletedSurvivalSource.FullyScreenedCoalescingClearingFamily.semanticLaw_coalescence`
uses the same actual source and no supplied replacement family.

The regression should still be encoded separately from the positive-minimum
source adapter.

## Scope and nonclaims

- No positive-gap reward table is constructed.
- Full screening under \(D_*>0\) is not consumed.
- A positive table-level marked gap is not confused with a nonvanishing
  whole-profile gain when \(M_n\to0\).
- The positive-debt postmark tail in the regression is not a global minimum.
- Host compression preserves opponents and the postmark tail, not the whole
  premark word.
- A carrier point is not called actual without the raw-diagonalization step.
