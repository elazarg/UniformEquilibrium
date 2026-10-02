# The strict pair-ray inert node: exact limits of local repair

Author: `ATLAS_GATEKEEPER`

## Status

No terminal approximation, charged return, or finite-rank regeneration is
proved here.  Two natural ways of consuming the strict normalized-pair
passport are ruled out exactly:

1. a uniformly bounded number of increasingly exact cap-prefix rows near the
   unique all-Continue cap has vanishing total absorption and vanishing total
   Bellman motion; and
2. the horizontal best-endpoint move which spends the fixed paid coordinate
   is not an admissible variation of the fixed-witness normalized-passport
   slice: it sets that witness's remaining gain to zero while global minimum
   debt keeps the target debt positive.

The second point remains true after adding the compact decorated-tail
provenance of
`FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY`.
Thus slice minimality and exact paid-coordinate elimination do not compose.

There is one positive exact identity worth retaining.  On the canonical
pure-pair maximal-prefix ray, the copied marked-row gain of the selected mover
is its entire whole-profile debt.  The endpoint update therefore kills that
coordinate exactly.  What remains uncontrolled is entry or cap lift in the
other three coordinates; after the update the target is outside the original
fixed-paid-witness slice.

The bounded-depth no-go is formalization-ready.  It is sharp in the sense
that uniqueness alone gives no linear absorption price: an explicit Fin4
root game below has all-Continue as its unique exact root and roots with
absorption of order `t` but total Nash defect exactly `3 t^2`.

## Question

Start from the off-minimum branch of the forced-pair maximal-prefix theorem:

* `D(z_infty)=L>D_* > 0`;
* the decorated source retains a minimum-debt post-pair tail, positive pure
  pair mass, and a fixed shifted paid mover gain;
* all-Continue is the unique exact cap--Nash root at `b_infty=z_infty.2`;
* future charge on the unchanged canonical ray vanishes.

Can these data produce terminal approximants, a charged exact return, or a
regenerated finite rank?  The results below identify operations which cannot
do so and the exact nonclosure left by the first horizontal update.

## 1. The canonical paid gain is the whole mover debt

Let `C` be the pure pair and let `Z_C` be its terminal semantic pair.  For a
player `p`, write

\[
\delta_p=
\max\{r_p(C\triangle\{p\})-r_p(C),0\}.
\tag{1}
\]

Since `|C|=2`, after every unilateral behavioral deviation at least one
member of `C` still Quits at date zero.  Thus the unrestricted behavioral cap
is the maximum of the two date-zero endpoint payoffs, and

\[
d_p(Z_C)=\delta_p.
\tag{2}
\]

On the canonical exact cap-prefix ray, let `alpha_k` be the reach of the
shifted pair row.  Exact cap-prefix debt scaling and literal payoff transport
give

\[
d_p(Z_k)=\alpha_k\delta_p,
\qquad
g_{k,p}=\alpha_k\delta_p.
\tag{3}
\]

Hence

\[
\boxed{g_{k,p}=d_p(Z_k).}
\tag{4}
\]

Let `Y_k` be the literal profile obtained by changing only `p`'s complete
strategy to the copied best endpoint at the shifted pair row.  Changing a
player's own prescribed strategy leaves that player's unrestricted cap
fixed.  The payoff rises by `g_{k,p}`.  Therefore

\[
\boxed{d_p(\operatorname{Sem}(Y_k))=0.}
\tag{5}
\]

This is stronger than the general endpoint identity “debt decreases by the
gain”: here the gain is the entire source debt.

If an arbitrary finite exact cap--Nash stack is subsequently prefixed above
`Y_k`, every coordinate debt is multiplied by the common Continue product.
Consequently `p` stays at zero throughout that stack and the positive-debt
support is fixed.  The checked debt-budget theorem also gives

\[
D_*\sum_t a_t\le D(Y_k)-D(\text{prefixed }Y_k).
\tag{6}
\]

This still does not yield support descent: the endpoint update can raise the
other three unrestricted caps, so neither `D(Y_k)\le D(Z_k)` nor no-new-debtor
is available.

The equality (4) uses the canonical exact ray above the date-zero pure pair.
It must not be asserted for an arbitrary raw finite prefix stored only in a
decorated orbit closure.  For such a prefix, the marked endpoint gain still
subtracts exactly from `p`'s debt, but an earlier deviation can make the whole
debt strictly larger than that marked gain.

## 2. Fixed-witness passport slices are not horizontally invariant

Consider a compact decorated prefix orbit carrying a nonnegative paid
coordinate `g` and impose the normalized condition

\[
g\ge\psi D(z),\qquad \psi>0.
\tag{7}
\]

This condition is exactly invariant under an exact cap--Nash prefix because
both sides scale by the joint Continue probability.  Minimizing `D` on the
slice therefore correctly forces every exact cap--Nash root at an off-minimum
minimizer to be all Continue.

Now perform the endpoint move represented by this fixed witness all the way
to its best endpoint.  At the updated marked row the same oriented witness
has remaining gain

\[
g'=0.
\tag{8}
\]

The target is an actual profile, so global positive minimum gives

\[
D(z')\ge D_*>0.
\tag{9}
\]

Equations (7)--(9) imply

\[
g'=0<\psi D(z').
\tag{10}
\]

Therefore

\[
\boxed{z'\text{ is outside the fixed-witness normalized-passport slice}.}
\tag{11}
\]

This is an exact incompatibility, not a missing estimate.  Minimality on the
slice gives no inequality for `D(z')` and no no-entry statement at `z'`.
In particular, (5) cannot be combined with slice minimality to infer a
minimum-fiber support drop.

One may enlarge the state by reselecting a fresh paid witness.  For a routed
nonsingleton pure coalition, the table-level toggle floor supplies a new
local paid row.  But this does not repair the full atlas step:

* if the pair mover leaves, the marked coalition is a singleton and the tail
  becomes behaviorally visible;
* the universal terminal gap supplies a paid deviation somewhere at the new
  actual profile, not a paid deviation co-realized at the marked row; and
* repeated reselection need not preserve a single positive normalized local
  gain threshold, because cross-coordinate cap lift can increase the new
  whole debt.

Thus a union over labels is a genuine enlargement of the obligation, not a
proof that the original compact slice is closed under its horizontal move.

## 3. Uniformly bounded local approximate repair is impossible

The following is the strongest consequence of unique all-Continue which does
not require a strict singleton gap.

### Proposition (bounded-depth robust inertness)

Let `b` be a payoff vector such that all-Continue is the unique exact product
root Nash equilibrium against `b`.  Fix `H<infinity`.  For every `n`, let

\[
q_{n,0},\ldots,q_{n,H-1}
\]

be product roots, let `b_{n,t}` be their displayed tail caps, and suppose

\[
\max_{t<H}\|b_{n,t}-b\|_\infty\longrightarrow0,
\qquad
\max_{t<H}\operatorname{Def}(b_{n,t},q_{n,t})longrightarrow0.
\tag{12}
\]

Then

\[
\max_{t<H}\operatorname{Abs}(q_{n,t})\longrightarrow0,
\qquad
\sum_{t<H}\operatorname{Abs}(q_{n,t})\longrightarrow0.
\tag{13}

If rewards and displayed tail payoffs are bounded by `M`, then

\[
\sum_{t<H}
\|F(q_{n,t};b_{n,t})-b_{n,t}\|_\infty
\longrightarrow0.
\tag{14}

Consequently a uniformly bounded-depth approximate cap-prefix word staying
near `b` cannot carry fixed positive charge, make fixed Bellman displacement,
promote a retained suffix atom into fixed fresh-root mass, or move an
off-minimum semantic point with debt `L>D_*` to the minimum fiber.

### Proof

Fix `eta>0`.  The robust absorption Nash-defect moat at the unique
all-Continue cap supplies a neighborhood of `b` and a number `c_eta>0` such
that every root with absorption at least `eta` has total defect at least
`c_eta`.  Equation (12) excludes such a root for all sufficiently large `n`,
uniformly over the finite set of indices `t<H`.  Since `eta` was arbitrary,
the maximum absorption tends to zero.  The sum has at most `H` terms, proving
(13).

The checked one-step successor estimate is

\[
\|F(q;v)-v\|_\infty\le2M\operatorname{Abs}(q)
\tag{15}
\]

after choosing a common bound.  Summation proves (14).  Continuity of
semantic and law prefixing then gives the last statement.

The proof is directly supported by
`exists_eventually_absorptionNashDefect_moat_of_unique_allContinue` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauNashMoat.lean`
and the successor-motion estimate in
`UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean`.

The word length being uniformly bounded is essential without an additional
linear absorption price.

## 4. Uniqueness alone has no linear absorption price

Here is an exact Fin4 boundary example.  Let players `0,1,2` have the cyclic
matrix

\[
A=
\begin{pmatrix}
0&1&-2\\
-2&0&1\\
1&-2&0
\end{pmatrix}.
\tag{16}
\]

For `i in {0,1,2}`, define

\[
r_i(S)=
\begin{cases}
\sum_{j\in S\cap\{0,1,2\},\ j\ne i}A_{ij},&i\in S,\\
0,&i\notin S.
\end{cases}
\tag{17}
\]

For player `3`, set `r_3(S)=-1` if `3 in S`, and `0` otherwise.  Take tail
payoff `b=0`.

Against a product root with Quit probabilities `(x,y,z,w)`, player `3`
strictly prefers Continue, so every exact root has `w=0`.  For the first
three players the Quit-minus-Continue endpoint differences are

\[
\Delta_0=y-2z,
\qquad
\Delta_1=z-2x,
\qquad
\Delta_2=x-2y.
\tag{18}
\]

All-Continue is the unique exact root.  Indeed:

* one positive coordinate makes the cyclic successor's difference strictly
  positive while that successor prescribes Continue;
* for two positive coordinates, one active coordinate has a strictly
  positive or strictly negative difference incompatible with its prescribed
  action;
* if all three coordinates lie strictly between zero and one, indifference
  would require
  `y=2z`, `z=2x`, and `x=2y`, hence `x=8x` and all are zero; and
* if one coordinate equals one, the next coordinate has strictly negative
  difference and must be zero, after which the preceding inactive coordinate
  has strictly positive difference.  Cyclic symmetry handles all cases.

For the symmetric root

\[
x=y=z=t,qquad w=0,qquad 0<t<1,
\]

all three differences equal `-t`.  Hence each coordinate defect is `t^2`,
so

\[
\boxed{operatorname{Def}(0,q_t)=3t^2,}
\tag{19}
\]

whereas

\[
\boxed{operatorname{Abs}(q_t)=1-(1-t)^3.}
\tag{20}
\]

Therefore

\[
{\operatorname{Def}(0,q_t)\over\operatorname{Abs}(q_t)}\longrightarrow0.
\tag{21}

So unique all-Continue does not imply any local inequality

\[
c\operatorname{Abs}(q)\le\operatorname{Def}(b,q)
\]

with `c>0`.  The strict-singleton-gap hypothesis in the checked linear-moat
theorem cannot be deleted merely because the exact root is unique.  The
example has global debt minimum zero and is not a quitting-game
counterexample; it tests only the proposed local inference.

It also explains the limitation of Proposition 3: with an unbounded number
of rows, defects of order `t^2` can in principle be accumulated over order
`1/t` rows while total defect tends to zero and total raw absorption remains
macroscopic.  An executable successor-linked chronology still requires a
separate Bellman-closure argument.

## 5. Interaction with the normalized-passport minimizer

The decorated normalized-passport minimizer is a valid strict contraction of
the support-entry alternative.  It proves that every exact cap-prefix
operation at its off-minimum minimizer is the all-Continue identity.  The
present audit adds:

1. approximate cap-prefix repairs of uniformly bounded depth also have
   vanishing charge and motion;
2. the fixed paid endpoint cannot be spent while remaining in the same
   positive-density fixed-witness slice; and
3. no arbitrary-depth linear toll follows from root uniqueness at the
   off-minimum cap.

Thus the supplied data do not yet force a consumer.  A successful next step
must provide at least one of the following genuinely new operations:

* an unbounded successor-linked repair with sublinear aggregate defect and a
  proved payoff seam (which would itself feed a charged near-return/terminal
  compiler);
* a renewable marked object, such as a source-matched response square, which
  survives after its first paid coordinate is spent;
* a horizontal endpoint theorem controlling all three nonmover cap lifts so
  that (5) becomes a minimum-fiber no-entry/support drop; or
* a new source-attached paid witness at the horizontal target, with one fixed
  normalized threshold and a well-founded rank.

Merely reapplying exact prefixes, appealing to the robust fixed-incidence
moat, or minimizing again on the same fixed-witness slice cannot do this.

## 6. Exact sources inspected

* `quittingTerminalSemanticDebt_pureSetRoot_eq` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
* exact playerwise and total cap-prefix debt scaling in the terminal-semantic
  prefix/debt modules used by
  `FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`;
* `exists_eventually_absorptionNashDefect_moat_of_unique_allContinue` and
  `exists_absorptionNashDefect_moat_of_unique_allContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauNashMoat.lean`;
* `exactCapPrefix_joint_eq_self_of_unique_allContinue` and
  `capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap` in
  `Research/Quitting/UniqueAllContinueCapStackNoGo.lean`;
* `semanticMinimum_mul_capNashStackAbsorptionSum_le_debtDrop` and
  `literalReset_capNashStack_debtBudget_or_identity` in
  `Research/Quitting/CapChangingLawRetainedSquareNoGo.lean`;
* the reviewed mathematical packets
  `FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md`,
  `FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`, and
  `FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY.md`.

## 7. Requested check

Please independently verify the unique-root case split in (18), the exact
scope of (4) for the canonical ray rather than an arbitrary decorated raw
prefix, and Proposition 3's use of a uniformly bounded row count.  In
particular, try to enlarge the passport slice so that the horizontal target
really remains inside with a fixed positive normalized threshold; a valid
enlargement must handle the leave-to-singleton endpoint without replacing the
marked-row paid witness by an unrelated terminal-gap witness.
