# Actual Zeno saturation splits into one-host compression or full screening

Author: `CODEX_AMPERE`

## Status

This note proves an exact non-scalar refinement of the scalar Zeno boundary
for the actual Fin4 forced-pair prefix orbit.

For a literal descendant, let `M` be the marked-pair mass and let `H_i` be
the probability that every opponent of player `i` survives to the marked
date.  Then

\[
\boxed{H_iH_j\le M\qquad(i\ne j).}
\]

Consequently every actual vanishing-`M` sequence has, after a subsequence,
exactly one of two forms:

1. **one-host:** one fixed `h` has `H_h` bounded away from zero and all other
   deleted reaches vanish; or
2. **fully screened:** every `H_i` vanishes.

The one-host arm has an actual source-attached producer.  Force `h` to
Continue through the retained premark word and choose its better Boolean
endpoint at the pure-pair mark.  This produces a fixed-mass marked atom,
preserves the postmark tail literally, and makes the marked `h`-defect zero.
Thus an actual infinite Zeno realization with persistent deleted reach exits
to a concentrated endpoint.

The fully screened arm is genuinely different.  The target/comparison law,
payoff, and every unrestricted cap coordinate coalesce, despite the fixed
pair label, the historical paid sibling, and the common literal tail.  An
explicit four-player quitting table below realizes this behavior, including
a unique all-Continue limiting cap root and a fixed positive-debt common
postmark tail.  Its global minimum is zero.  Therefore **positive global
minimum provenance is the one field not reproduced by the regression**.

This is not a terminal consumer for the fully screened arm.  It replaces the
undifferentiated scalar Zeno residual by a finite actual passport:

\[
\boxed{
\text{source-attached host-compressed atom}
\quad\lor\quad
\text{fully screened premark escape}.}
\]

The first disjunct is a producer.  The second is an exact residual plus a
sharp actual zero-minimum regression, not a verifier pretending to consume
the positive-minimum source.

## Question

Can the scalar saturated-halving chain in
`FIN4_NORMALIZED_INERT_SINGLE_DENSITY_TOLL_AND_ZENO_BOUNDARY.md` be realized
indefinitely by actual descendants of the fixed Fin4 forced-pair source once
the cap vector, full law, fixed labels, paid sibling, and literal source word
are retained?

The result below answers all cases except the fully screened one.  It also
shows that the omitted non-scalar data alone do not eliminate full screening.

## Sources inspected

- `exports/FIN4_NORMALIZED_INERT_SINGLE_DENSITY_TOLL_AND_ZENO_BOUNDARY.md`;
- `notes/CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL.md`;
- `Research/Quitting/NormalizedPassportPrefixOrbit.lean`;
- `Research/Quitting/NormalizedPassportMinimizer.lean`;
- `Research/Quitting/NormalizedPassportMinimumReturn.lean`;
- `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`;
- `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`;
- `Research/Quitting/PaidNonexactCapStackAccount.lean`;
- `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`;
- `UniformEquilibrium/Quitting/Root/TerminalDebtGreenAccount.lean`;
- `notes/CODEX_POINCARE__PREMARK_BUBBLE_CAP_HOLONOMY.md`; and
- `notes/PAIR_WALL_REVIEW__POSITIVE_MINIMUM_CANONICAL_RAY_CYCLE.md`.

The common-prefix cap formula and pass-through/exceptional-owner viewpoint
already occur in the Poincare and persistent-clock work.  The new point here
is their exact finite-word specialization to normalized-passport descendants,
the pairwise inequality `H_i H_j <= M`, the corresponding source-attached host
compression, and the full actual regression for the remaining screened arm.

## 1. The deleted-survival passport of a literal word

Fix a literal actual descendant of the forced-pair family.  Include both the
new arbitrary prefix roots and the originating profile's roots strictly
before the marked date in one finite premark word.  For each player `i`, let

\[
S_i:=\Pr(i\text{ Continues at every root of the premark word}).
\tag{1}
\]

Behavioral product independence gives

\[
M=\prod_{i\in I}S_i,
\tag{2}
\]

because the marked root is a pure nonempty pair: its unconditional coalition
mass is exactly the probability of reaching it.  For player `i`, define the
deleted or opponent reach

\[
H_i:=\Pr(\text{every opponent of }i\text{ Continues through the word})
    =\prod_{k\ne i}S_k.
\tag{3}
\]

This is precisely the coefficient through which a continuation perturbation
can enter player `i`'s unrestricted cap calculation.  Equations (2)--(3)
immediately give, for distinct `i,j`,

\[
\begin{aligned}
H_iH_j
 &=\left(\prod_{k\ne i}S_k\right)
   \left(\prod_{k\ne j}S_k\right)\\
 &=M\prod_{k\ne i,j}S_k\\
 &\le M.
\end{aligned}
\tag{4}
\]

No division or positivity assumption is used in (4).  When `H_i>0`, there is
also the exact identity

\[
S_i=\frac{M}{H_i}.
\tag{5}
\]

### Carrier-to-raw diagonalization

A saturated carrier point need not itself be actual.  Suppose, however, that
an alleged infinite saturated chain consists of closed-orbit points `P_n`
with `M(P_n)>0` and `M(P_n)->0`.  Since the orbit carrier is the closure of
the raw decorations, choose a raw decoration `X_n` sufficiently close to
`P_n` in all stored decoration fields and with

\[
|M(X_n)-M(P_n)|<\min\{1/n,M(P_n)/2\}.
\tag{6}
\]

Then `X_n` is a literal source descendant, `M(X_n)>0`, and `M(X_n)->0`.
Its vector `(H_i(X_n))_i` belongs to the compact cube `[0,1]^4`; take a
convergent subsequence.  Thus the following split applies to every actual
realization of infinite carrier saturation.  The deleted reaches need not be
added to the carrier topology to obtain the split; they are extracted from
the selected raw words.

## 2. Exact screened-or-one-host dichotomy

Let `M_n->0` for a sequence of actual literal descendants.  After passing to
a subsequence, assume

\[
H_{i,n}\longrightarrow h_i\qquad(i\in\operatorname{Fin}4).
\]

Taking limits in (4) gives

\[
h_ih_j=0\qquad(i\ne j).
\tag{7}
\]

Hence at most one `h_i` is positive.

### Fully screened arm

If every `h_i=0`, then

\[
\boxed{H_{i,n}\to0\quad\text{for every }i.}
\tag{8}
\]

### One-host arm

Otherwise there is one fixed player `h` and an `eta>0` such that, after
discarding finitely many terms,

\[
H_{h,n}\ge\eta.
\tag{9}
\]

For `i != h`, (4) gives

\[
H_{i,n}\le\frac{M_n}{H_{h,n}}
          \le\frac{M_n}{\eta}\longrightarrow0,
\tag{10}
\]

and (5) gives

\[
S_{h,n}=\frac{M_n}{H_{h,n}}\longrightarrow0.
\tag{11}
\]

Thus the literal obstruction has a finite label: either no unilateral
deletion can see the remote mark, or exactly one fixed host can.

## 3. The one-host arm produces a concentrated endpoint

Fix a one-host descendant.  Let `C` be its pure marked pair and `tau` its
literal postmark behavioral tail.  Construct a new profile as follows.

1. Keep every opponent of `h` unchanged through the entire premark word.
2. Force `h` to Continue through that word.
3. At the marked row, let `h` take whichever of its two pure Boolean
   endpoints maximizes its payoff against the actual root of the other
   players and the actual tail `tau`.
4. Leave the profile strictly after the mark unchanged.

The modified profile reaches the marked row with probability exactly `H_h`.
The new pure marked coalition is either `C`, `C minus {h}`, or
`C union {h}`.  It is
never empty because `|C|=2`.  Therefore the marked terminal atom has mass

\[
\boxed{H_h\ge\eta.}
\tag{12}
\]

By construction, the marked root coordinate Nash defect of `h` is exactly
zero.  The complete postmark behavioral profile, its semantic pair, and its
full law are literally the old tail's.  The fixed original source, raw word,
comparison/target labels, and chronology remain available as provenance;
only `h`'s premark actions and its marked endpoint were changed.

This is an actual producer, not a supplied-object test:

\[
\boxed{
\text{one-host Zeno descendant}
\Longrightarrow
\text{source-attached concentrated marked endpoint of mass }\eta.}
\tag{13}
\]

It does **not** prove that the new whole semantic pair is near the global
minimum, or that the other three whole-profile caps do not rise.  Any
downstream consumer needing those properties still requires an adapter.  But
the scalar density cannot keep halving while a deleted reach stays positive:
the actual source word itself supplies a fixed-resolution escape.

## 4. Full screening makes the paid siblings semantically invisible

Let `T_n` and `S_n` be the actual target and comparison siblings with the same
premark word and postmark tail, differing only in the gain mover's endpoint at
the marked row.  Let the corresponding pure coalitions be `C` and
`C minus {o}`, and assume rewards have absolute value at most `R`.

Their prescribed payoff difference is exact:

\[
U_i(T_n)-U_i(S_n)
 =M_n\bigl(r_i(C)-r_i(C\setminus\{o\})\bigr).
\tag{14}
\]

Their terminal laws differ only on those two marked outcomes.  Thus their
total-variation distance is `M_n` (their `ell^1` distance is `2M_n`).

For `i=o`, the opponents are identical, so own-strategy invariance gives

\[
B_o(T_n)=B_o(S_n).
\tag{15}
\]

For `i != o`, fix any behavioral deviation of `i` and couple the two opponent
profiles.  The deviator can distinguish the siblings only if all of its
opponents survive to the marked row, an event of probability `H_{i,n}`.
Payoffs differ by at most `2R` on that event.  Taking the supremum over all
behavioral deviations yields

\[
|B_i(T_n)-B_i(S_n)|\le2R H_{i,n}.
\tag{16}
\]

Equations (14)--(16) are the actual-word form of the common-prefix cap
commutator.  In the fully screened arm,

\[
\|U(T_n)-U(S_n)\|_\infty\to0,
\qquad
\|B(T_n)-B(S_n)\|_\infty\to0,
\tag{17}
\]

and their whole laws coalesce.  Their postmark semantic/law tail is already
equal exactly.  The historical paid equality `G_n=Delta M_n` survives, but
both sides vanish.

More generally, replacing the entire remote marked continuation by any other
bounded continuation changes prescribed payoff by `O(M_n)` and coordinate
`i`'s cap by `O(H_{i,n})`.  Hence full screening collapses all the apparent
non-scalar endpoint data to a prefix-only escape object.

## 5. An actual Fin4 fully screened regression

This section proves that full screening is not ruled out by product
realizability, fixed pair labels, an actual paid sibling, a positive-debt
common tail, or unique all-Continue at the limiting cap.

Let the players be `0,1,2,3`.  For every nonempty coalition `A`, define

\[
r_i(A)=
\begin{cases}
-1,&i\in A,\\
0,&i\notin A,
\end{cases}
\tag{18}
\]

except for the single coordinate

\[
r_1(\{0,1\})=1.
\tag{19}
\]

Thus the fixed paid gap is

\[
r_1(\{0,1\})-r_1(\{0\})=1.
\tag{20}
\]

First fix one literal base comparison/target pair.  At its marked date zero,
the comparison plays the pure singleton `{0}` and the target plays the pure
pair `{0,1}`.  Attach the same fixed postmark tail to both.  For a positive-
debt choice, take the pure-singleton `{0}` profile as that tail; its total
debt is `2`: player `0` can Continue to zero instead of receiving `-1`, and
player `1` can join to receive `1` instead of `0`.

For `n>=2`, put `epsilon_n=1/n` and prefix **both fixed base profiles** by a
common length-`n` product word.  In that word, each player has the independent
premark clock

\[
\Pr(T_i=t)=p_n:=\frac{1-\epsilon_n}{n}
\quad(0\le t<n),
\qquad
\Pr(T_i\ge n)=\epsilon_n.
\tag{21}
\]

These clocks have the standard behavioral hazard realization.  If all four
players survive the word, the already-fixed base profiles execute their
singleton/pair marked roots at shifted date `n`.  Thus this is literally one
fixed decorated base row under a sequence of common raw prefix words, not a
freshly selected endpoint family.

The marked mass and deleted reaches are

\[
M_n=\epsilon_n^4=\frac1{n^4},
\qquad
H_{i,n}=\epsilon_n^3=\frac1{n^3}
\quad\text{for every }i.
\tag{22}
\]

Hence this is fully screened.  The actual target-minus-comparison gain of
player `1` is exactly

\[
G_n=M_n.
\tag{23}
\]

At the target marked pair, player `1` receives `1` by Quitting and `0` by
Continuing while player `0` still Quits.  Its marked coordinate defect is
therefore exactly zero.

### Terminal-law limit

A nonsingleton premark terminal coalition requires at least one pair of
players to choose the same finite date.  By the union bound,

\[
\Pr(\text{a finite tie})
 \le {4\choose2}\sum_{t<n}p_n^2
 =6np_n^2
 \le\frac6n.
\tag{24}
\]

The probability of reaching the remote mark is `epsilon_n^4`.  By symmetry,
the four premark singleton probabilities are equal.  Equations (22) and (24)
therefore imply that both siblings' terminal laws converge to the uniform law
on the four singleton coalitions.

### Prescribed-payoff limit

For `i != 1`, the payoff is `-1` exactly when `i` belongs to the terminal
coalition and is zero otherwise.  For player `1`, the only exception is the
coalition `{0,1}`; its probability is at most the tie bound plus `M_n`.
It follows that for both siblings

\[
U_i\longrightarrow-\frac14
\qquad(i=0,1,2,3).
\tag{25}
\]

### Full behavioral cap limit

For `i != 1`, Never gives zero, and every payoff obtained on an event where
`i` quits is `-1`.  Hence

\[
B_i=0
\qquad(i\ne1)
\tag{26}
\]

exactly.

For player `1`, Never also gives zero.  Before the remote mark, a pure quitting
date gives positive payoff only on the event that exactly player `0` quits
with it while players `2,3` Continue.  That event has probability at most
`p_n<=1/n`.  At the remote date, its payoff from joining player `0` is at most
the opponents' survival probability `epsilon_n^3`.  Later quitting dates are
preempted by player `0`.  Since every behavioral strategy is a mixture of its
complete pure quitting times and Never along the unique live history,

\[
0\le B_1\le\max\{p_n,\epsilon_n^3\}\le\frac1n.
\tag{27}
\]

Thus the two semantic pairs converge to

\[
\left(
(-1/4,-1/4,-1/4,-1/4),
(0,0,0,0)
\right),
\tag{28}
\]

whose total debt is `1`.

### Unique all-Continue limiting cap root

Against continuation cap `b=0`, players `0,2,3` receive `-1` whenever they
Quit and `0` whenever they Continue.  Hence every cap--Nash root sets their
Quit probabilities to zero.  With those three players Continuing surely,
player `1` receives `r_1({1})=-1` by Quitting and zero by Continuing.  It too
must Continue.  Therefore all-Continue is the unique exact cap--Nash root at
the limiting cap.

Nevertheless all-Never is an actual exact terminal Nash profile for this
table, so the global minimum debt is

\[
D_*=0.
\tag{29}
\]

The regression therefore realizes, in an actual four-player quitting game:

- fixed target/comparison labels `{0,1}` and `{0}`;
- the exact positive table gap `Delta=1` and actual gain `G_n=M_n>0`;
- one fixed decorated source/target base and literal common prefix words;
- a common fixed positive-debt postmark tail;
- full screening `H_{i,n}->0`;
- coalescence of complete semantic pairs and laws; and
- unique all-Continue at the limiting cap.

It does not realize positive global minimum.  Thus an argument eliminating
fully screened Zeno must use the minimum provenance quantitatively; none of
the other listed non-scalar fields suffices.

## 6. Exact remaining positive-minimum interface

The actual realizability problem has now narrowed to the following statement.
Let a fixed positive-minimum forced-pair source produce raw descendants with

\[
M_n\to0,\qquad H_{i,n}\to0\quad\text{for every }i.
\tag{30}
\]

Then their remote pair/comparison data are invisible to all prescribed
payoffs, caps, and laws by (14)--(17).  To rule this out, positive minimum must
force one of:

1. a fixed `i` and `eta>0` with `H_{i,n}>=eta`, which is immediately consumed
   by the host compression of Section 3;
2. a source-faithful return before the fully screened prefix;
3. a support/rank regeneration using the prefix-only semantic limit; or
4. a contradiction between full screening and the retained global-minimum
   / terminal-witness data.

Equivalently, the finite additional passport is the deleted-survival vector

\[
\boxed{(H_0,H_1,H_2,H_3).}
\tag{31}
\]

It is produced by every literal raw word.  Its positive-coordinate arm has an
actual concentrated-endpoint consumer.  Its zero-limit arm is the sole
remaining Zeno actualization problem.

This is stronger than appending another scalar density verifier: it identifies
which unilateral deviation can still see the marked source and performs the
corresponding literal modification.  It is weaker than a full solution because
the regression proves that the all-zero limit is compatible with every field
except positive global minimum.

## Lean-facing formulation

A useful formal interface would first define, for a literal finite root word,

```text
quittingPlayerWordSurvival roots i
quittingDeletedWordSurvival roots i
```

and prove

```text
deletedWordSurvival_mul_deletedWordSurvival_le_joint
vanishingJoint_deletedSurvival_subseq_screened_or_uniqueHost
hostCompression_concentratedEndpoint
fullyScreened_comparison_semanticLawDist_tendsto_zero
```

The first theorem is the division-free identity (4).  The host theorem should
return the actual modified profile, marked coalition, mass floor, zero local
defect, postmark-spine equality, and the originating raw decoration.  It
should not claim whole-profile near-minimality or no cap leakage.

The regression is ordinary mathematics only and has not been encoded in Lean.

## Nonclaims

- No positive-gap reward table is constructed.
- The fully screened arm is not consumed.
- A positive marked table gap is not confused with a nonvanishing actual
  payoff gain when `M_n->0`.
- The positive-debt postmark tail in the regression is not a global minimum.
- Host compression does not preserve the whole premark word literally; it
  preserves the opponents, postmark tail, and an exact pointer to the source
  word.
- No carrier point is called actual without the raw diagonalization step.
