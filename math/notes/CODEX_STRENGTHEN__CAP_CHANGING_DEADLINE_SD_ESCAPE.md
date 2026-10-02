# Cap-changing deadline re-equilibration still forces retained-tail escape

Author: `CODEX_STRENGTHEN`

Status: **complete positive-minimum no-go for every fixed-depth-growing,
source-faithful cap-complete deadline inverse system, plus a finite
marked-atom/seam-budget rank forcing a bounded-depth grammar exit; ordinary
mathematics with checked scalar ingredients and a precise Lean handoff; not
an export proposal.**

This continues
[`CODEX_STRENGTHEN__FINITE_DEADLINE_HIGH_TO_LOW_EDGE_BARRIER.md`](CODEX_STRENGTHEN__FINITE_DEADLINE_HIGH_TO_LOW_EDGE_BARRIER.md)
and
[`CODEX_STRENGTHEN__POSITIVE_MINIMUM_HARD_RESIDUAL_ENDPOINT_BARRIER.md`](CODEX_STRENGTHEN__POSITIVE_MINIMUM_HARD_RESIDUAL_ENDPOINT_BARRIER.md).
It implements the architectural retry in which increasing the deadline may
re-equilibrate **every** earlier root and may change every intermediate cap.

## 1. Answer

Re-equilibrating the whole prefix does not cure the source-faithful retained
tail obstruction.  Exact cap scaling and the positive global debt minimum
give a uniform lower bound on the probability of reaching the retained tail,
independent of how all earlier roots are reselected.  If the retained source
contains a finite marked atom of fixed positive mass, a length-`N` word moves
that atom beyond date `N` while retaining fixed mass.  Hence no cofinal family
is total-variation Cauchy, and no summable decoder (`SD`) can realize it as one
actual source-attached behavioral profile.

This remains true for vanishing approximate cap/Bellman errors.  A summable
triangular payoff-and-cap seam budget cannot help: once its debt error is less
than half the positive minimum, the same uniform return floor reappears.

There is an even simpler positive-minimum regression against a semantic-only
decoder.  All-Continue padding can make **every payoff and unrestricted-cap
seam exactly zero** while shifting the retained finite atom to infinity.
Thus a payoff+cap seam budget without a stopping-law/tightness passport is not
an actual decoder.

The no-go is conditional on the exact positive-minimum/hard-atom source used
by the current Fin4 strict-ray packet; it does not construct a counterexample
reward table.  Unlike the censored-clock regression, it assumes `D_*>0`
throughout.

## 2. Cap-changing deadline states

Fix a finite nonempty player set `I`, a quitting reward table bounded by
`R>0`, and

\[
 D_*:=\inf_\sigma D(\sigma)>0,
 \qquad
 D(\sigma)=\sum_i(B_i(\sigma)-U_i(\sigma)).          \tag{2.1}
\]

No compatibility between the roots at different levels is assumed.  At
level `N`, choose:

* an arbitrary actual retained tail `Y_N`;
* an arbitrary root word
  `W_N=[q^N_0,...,q^N_(ell_N-1)]` with `ell_N>=N`;
* the literal head `X_N=W_N*Y_N`;
* exact cap--Nash certification of every root against its actual remaining
  suffix.

Thus `W_N` may be a completely re-equilibrated replacement of `W_(N-1)`.
Every intermediate cap may change.  The only cross-level datum retained is
the source atom described below.

Write

\[
 C_N=\prod_{t<\ell_N}
       \Pr_{q^N_t}(\text{all Continue}).             \tag{2.2}
\]

Exact cap chronology gives

\[
 D(X_N)=C_ND(Y_N).                                   \tag{2.3}
\]

The checked source is
`quittingTerminalDebtSum_capNashRootStack_eq` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`.

Since prescribed payoffs and unrestricted caps both lie in `[-R,R]`,

\[
 0\le D(Y_N)\le D_{\max}:=2|I|R.                    \tag{2.4}
\]

Equations (2.1)--(2.4) imply the selection-independent return floor

\[
 C_N={D(X_N)\over D(Y_N)}
 \ge {D_*\over D(Y_N)}
 \ge q_*:={D_*\over2|I|R}>0.                        \tag{2.5}
\]

This is the key point: changing all earlier roots does not change the lower
bound.  It uses only literal cap chronology, bounded rewards, and the global
positive minimum.

## 3. The retained-atom hypothesis

Assume the source ancestry at level `N` records a nonempty coalition `S`, a
finite tail date `s_N`, and an event `A_N` under `Y_N` such that

\[
 \Pr_{Y_N}(A_N)\ge m>0,                              \tag{3.1}
\]

and on `A_N` the terminal quitting coalition is `S` at tail date `s_N`.
The date may vary with `N`; only finiteness and the uniform mass floor matter.

Literal grafting transports this exact event to the event that every root in
`W_N` Continues and then `A_N` occurs.  Its probability under `X_N` is

\[
 C_N\Pr_{Y_N}(A_N)\ge q_*m,                         \tag{3.2}
\]

and its absolute date is `ell_N+s_N>=N`.  In particular, for every `i in S`
and every fixed cutoff `T`, all `N>T` satisfy

\[
 \Pr_{X_N}(T_i>T,\ T_i<\infty)\ge q_*m.             \tag{3.3}
\]

Nothing in this calculation remembers the old roots.  It survives arbitrary
cross-level re-equilibration.

## 4. Re-equilibrated deadline escape theorem

### Theorem 4.1

Under (2.1)--(3.1), the marginal stopping laws of `X_N` for every `i in S`
have:

1. no total-variation-convergent cofinal subsequence;
2. no common finite-tail tightness envelope; and
3. no summable adjacent total-variation seam budget.

More precisely,

\[
 \sum_Nd_{\rm TV}
   (\operatorname{Law}_{X_{N+1}}(T_i),
    \operatorname{Law}_{X_N}(T_i))=\infty.           \tag{4.1}
\]

**Proof.**  The absence of finite-tail tightness is (3.3).  Suppose a cofinal
subsequence converges in total variation to a probability law `lambda` on
`N union {infinity}`.  For

\[
 F_T=\{t\in\mathbb N:t>T\},
\]

total-variation convergence and (3.3) give
`lambda(F_T)>=q_*m` for every `T`.  But `F_T` decreases to the empty set, so
continuity from above gives `lambda(F_T)->0`, a contradiction.

If the series in (4.1) were finite, its tails and the triangle inequality
would make the marginal laws total-variation Cauchy.  Probability laws on a
countable set are complete in total variation, hence they would converge,
contradicting the first part.  \(\square\)

The proof is stronger than a regression table: it applies inside every
hypothetical positive-minimum Fin4 source carrying the retained atom.

## 5. No `SD` decoder

An `SD` trace decoder requires finite representatives `Z_N` with a uniformly
summable triangular source-law error, in particular

\[
 \sum_N d_{\rm TV}(Z_{N+1},Z_N)<\infty              \tag{5.1}
\]

at every source port whose literal ancestry is to survive.  It may also allow
vanishing reconstruction errors

\[
 d_{\rm TV}(Z_N,X_N)\longrightarrow0.               \tag{5.2}
\]

Equations (5.1)--(5.2) are impossible.  The first makes `Z_N` Cauchy; the
second then makes `X_N` Cauchy.  This contradicts Theorem 4.1.

Consequently, no variational selection of the Nash correspondence, no global
cross-level action minimizer, and no replacement of all earlier roots can
produce an actual `SD` decoder while retaining (3.1).  The obstruction is
selection-independent.

This does not forbid a semantic compact limit.  It forbids identifying such a
limit with an actual behavioral descendant carrying the displayed source
atom.

## 6. Vanishing approximate cap seams do not help

Suppose exact scaling (2.3) is weakened to the one-sided folded-debt estimate

\[
 D(X_N)\le C_ND(Y_N)+e_N,
 \qquad e_N\longrightarrow0.                        \tag{6.1}
\]

Any proposed approximate-cap compiler whose triangular payoff+cap budget is
claimed to approximate the exact folded cap chronology must in particular
give such an `e_N`, because total debt is a finite sum of cap-minus-payoff
coordinates.  Cross-level semantic seams by themselves do not imply (6.1);
Section 7 shows why that weaker datum is insufficient even when it vanishes.

From (2.1), (2.4), and (6.1),

\[
 C_N\ge {D_*-e_N\over D_{\max}}.                    \tag{6.2}
\]

For all sufficiently large `N`, `e_N<=D_*/2`, and therefore

\[
 C_N\ge {D_*\over2D_{\max}}
       ={D_*\over4|I|R}>0.                          \tag{6.3}
\]

Replacing `q_*` by the last constant in Sections 3--5 proves the same escape
and `SD` impossibility.  Thus an approximate cap-changing inverse system can
erase the retained tail only by paying order-one debt error infinitely often.
That is incompatible with a summable triangular seam budget.

This is the requested coercivity invariant: **retained-tail reach is bounded
below by positive debt minus the current total semantic seam**.  It is not a
real-valued capacity used as a rank.

## 7. Exact zero-semantic-seam regression

The need for a clock/tightness passport is visible even without changing any
cap.  Let `Y` be an actual positive-debt tail carrying a finite atom of mass
`m>0`, and suppose all Continue is an exact cap root over `Y`.  This is the
local situation in the positive-minimum strict all-Continue basin.  Put

\[
 X_N=\underbrace{\mathbf C\star\cdots\star\mathbf C}_{N\text{ roots}}
      \star Y.                                      \tag{7.1}
\]

Then for every `N`:

\[
 U(X_N)=U(Y),\qquad B(X_N)=B(Y),\qquad D(X_N)=D(Y).  \tag{7.2}
\]

All payoff seams, all unrestricted-cap seams, all debt seams, and all
cap--Nash defects are exactly zero.  Nevertheless the marked atom occurs at
date `N+s`, so Theorem 4.1 applies with `C_N=1`.

This is a positive-minimum-compatible regression schema against the claim

```text
summable payoff seams + summable cap seams
    => source-faithful actual SD decoder.
```

The false implication remains false even with **zero** semantic seams.  The
missing datum is stopping-law tightness, not a sharper semantic norm.

The schema does not assert a standalone Fin4 counterexample table.  In the
current hypothetical no-UE branch, the near-minimum cap basin supplies the
all-Continue exactness and the strict-ray source supplies the retained hard
atom.  That is exactly the provenance under audit.

## 8. Application to the source-facing Fin4 strict ray

The source-facing packet in
`formalized/POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE.md` has a rank-`N` base
profile containing a sure fixed pure-pair row, followed by its counterfactual
continuation.  Its reverse maximal exact-root word is literally grafted in
front of that base.  Thus (3.1) holds with the fixed pair and a uniform
positive mass (indeed the row itself is sure before multiplication by the
root-word return).

Theorem 4.1 shows more than the fixed selected ray theorem: **any** replacement
of the rank-`N` root word by a new length-at-least-`N` exact cap--Nash word
over the same retained base packet still escapes.  The roots need not agree
at any earlier date and need not be selected by the maximal-absorption rule.

Accordingly, a cap-changing projective deadline system has only the following
escapes from the no-go:

1. discard or shrink the retained hard atom, breaking source ancestry;
2. let the terminal debt become unbounded, impossible under bounded rewards;
3. permit order-one cap/Bellman debt error, breaking summable seams;
4. keep the executable depth uniformly bounded, abandoning the inverse-depth
   construction; or
5. perform a finite actual reset which moves the source tail back to a bounded
   date and pay that reset by a separate terminal/rank theorem.

The fifth item is exactly the endpoint-matched regeneration problem; calling
it a projective restriction map does not construct it.

## 9. Consequence for adjacent-deadline selection

Ordinary hard-deadline Nash laws avoid the retained-tail return floor because
their `Never` outcome is hard zero, not an actual source tail.  They can be
compactly compared across censor maps, but their roots are not cap-complete.

Cap-terminal timing laws repair this: the all-`Never` terminal value is
`B(Y_N)`.  As shown in Section 11 of the linked note, under `D_*>0` every
cap-terminal mixed Nash law has positive joint return and compiles to an exact
cap--Nash stack.  The repair therefore places it under Theorem 4.1.  One
cannot have all three of:

```text
exact unrestricted-cap completeness,
literal retained-source ancestry of growing depth,
summable total-variation triangular seams.
```

Re-equilibrating earlier dates changes none of these three facts.

## 10. Lean handoff

The generic exact theorem should be independent of Fin4:

```text
theorem no_summableTV_reEquilibrated_capNashStacks_of_positiveDebtInf
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hreward : forall terminal player, |reward terminal player| <= R)
    (hlength : forall N, N <= (roots N).length)
    (hstack : forall N,
      IsQuittingCapNashRootStack reward (roots N) (tail N))
    (hatom : ... uniform finite marked tail atom of mass at least m ...) :
    not Summable (fun N =>
      pmfTV (stoppingLaw (head (N+1)) i) (stoppingLaw (head N) i))
```

The proof uses:

* `quittingTerminalDebtSum_capNashRootStack_eq`;
* the standard reward-bound bounds on prescribed payoff and cap;
* the literal root-stack joint-survival product;
* the root-stack shift/marked-event identity; and
* completeness of PMFs in total variation, or the decreasing events `F_T`
  argument in Theorem 4.1.

An approximate wrapper should assume (6.1) directly and conclude the same
result once `e_N -> 0`.

A separate semantic regression declaration can specialize every root to
all Continue and state (7.2) together with non-tightness of the shifted marked
atom.  No new stopping-time type is required.

The cap-terminal compiler proposed in the linked note should be formalized
only if this finite-deadline architecture is pursued.  Its useful zero-return
lemma is:

```text
capTerminalTimingNash_jointReturn_zero_imp_terminalDebtSum_zero
```

and the positive-minimum corollary says every such Nash law has positive
joint return and compiles to `IsQuittingCapNashRootStack`.

## 11. Checked sources and status

Checked declarations inspected:

* `quittingTerminalDebtSum_capNashRootStack_eq` and
  `capNashRootStack_continueMass_pos_of_debtSumInf_pos`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
* `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
* `quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none` and
  the finite timing realization identities,
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingRealization.lean`;
* `QuittingExactStationaryNashBellmanReturn.root_eq_allContinue_of_no_uniformPayoff`,
  `Research/Quitting/ExactNashBellmanRepairReturnTrichotomy.lean`;
* the checked declarations listed in
  `formalized/POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE.md` for the actual
  source-facing fixed-pair ray.

Theorem 4.1 and the approximate extension in Section 6 are ordinary
mathematics, not currently named Lean theorems.  They are direct finite-product
and probability arguments.  No literature claim is used.

## 12. Final residual

The requested cap-changing `SD` deadline decoder does not exist if it retains
the positive-minimum source atom behind unbounded executable depth.  The
remaining finite producer must stop at a finite depth and execute an actual
reset/restart there.  Such a reset must either:

* be paid by the high-to-near-minimum debt edge of the preceding note;
* decrease a separately renewable discrete source rank; or
* compile directly to a uniform-equilibrium payoff.

No inverse-system selection rule can substitute for that finite operation,
because the obstruction above is uniform over all root selections.

## 13. Finite bounded-depth alternative

The escape theorem can be used constructively.  It does not ask an execution
to converge after shifting the marked atom.  Instead it gives every neutral
deadline epoch a finite clock and charges every restart of that clock to the
decoder's seam budget.

### 13.1 One finite epoch

Let `A` be the actual profile at the start of an epoch and fix one marked
player `i in S`.  Put

\[
 \theta=q_*m>0.                                     \tag{13.1}
\]

Choose a finite cutoff `T(A)` so that

\[
 \Pr_A(T_i>T(A),\ T_i<\infty)<\theta/4.             \tag{13.2}
\]

Such a cutoff exists for every actual stopping law.  Any neutral
cap-complete descendant `X` which retains the marked atom behind more than
`T(A)` new roots satisfies

\[
 \Pr_X(T_i>T(A),\ T_i<\infty)\ge\theta.             \tag{13.3}
\]

Therefore

\[
 d_{\rm TV}(A_i,X_i)>3\theta/4.                     \tag{13.4}
\]

By the triangle inequality, the sum of the actual marginal-TV seams along
**any** re-equilibration path from `A` to `X` is greater than
`3 theta / 4`.  The roots may all change at every step.

This gives the finite local alternative:

> Before neutral executable depth exceeds `T(A)`, the repair either outputs
> a terminal approximation, a charged return, or a strict renewable source
> rank/support drop; otherwise that finite epoch consumes more than
> `3 theta / 4` of the decoder's law-seam budget.

The three productive outputs are not deduced from probability alone; they
must be the nonneutral branch tags of the proposed repair grammar.  What is
deduced is that “extend the deadline and re-equilibrate again” cannot remain a
free fourth branch.

### 13.2 Restarts and a discrete rank

Suppose an `SD` certificate gives a finite upper bound `B` on the total
marginal-TV seam budget along one execution.  Allow a restart after an epoch:
the endpoint becomes a new actual anchor, a fresh cutoff is selected by
(13.2), and the local deadline counter is reset.

Every completed neutral epoch costs more than `3 theta / 4`, hence certainly
more than `theta / 2`.  The number of such restarts is at most

\[
 K=\left\lfloor {2B\over\theta}\right\rfloor.       \tag{13.5}
\]

This yields a genuinely well-founded, discrete execution rank.  During epoch
`e`, after `n` neutral extensions, use

\[
 \rho(e,n)=\bigl(K-e,\ T(A_e)-n\bigr)               \tag{13.6}
\]

in lexicographic order on `N x N` (with the second coordinate truncated at
zero).  A neutral deadline extension decreases the second coordinate.  A
restart decreases the first coordinate and may reset the second.  Once the
first coordinate is exhausted, another neutral restart would exceed `B`, so
the grammar must take a productive finite branch.

This is not the real hazard capacity disguised as a rank.  Its first
coordinate counts fixed quanta of the **actual decoder seam budget** forced
by the marked finite atom; its second is a finite stopping-law tightness
cutoff of one actual anchor.

### Theorem 13.1: finite exit for any cap-changing deadline repair

Consider a source-faithful repair grammar with these properties:

1. every neutral extension is a finite actual cap-complete word and retains
   the marked tail atom with the floor `m`;
2. the execution carries actual marginal-TV seams with total bound `B`;
3. before a local cutoff expires, the grammar may output one of
   `Terminal`, `ChargedReturn`, or `StrictRankDrop`;
4. at cutoff expiry it either outputs one of those tags or starts a new epoch
   at the actual endpoint.

Then every execution outputs a productive tag after finitely many operations.
More precisely it uses at most `K` complete neutral restarts, with `K` as in
(13.5), and each epoch has the finite local depth bound `T(A_e)`.

**Proof.**  If an epoch passes its cutoff without a productive tag, (13.4)
charges more than `theta/2` to its disjoint segment of the seam series.
There can be at most `K` such segments.  In the next epoch the finite second
coordinate in (13.6) cannot be reset again, so one of the productive tags is
forced.  Equivalently, the lexicographic rank (13.6) strictly decreases at
every neutral extension or restart.  \(\square\)

### 13.3 Source-facing Fin4 specialization

For the strict maximal-prefix packet, `rayBaseProfile_stageMass_eq_one`,
`rayBaseProfile_outcomeMass_eq_pointMass`, and
`rayBaseProfile_terminalMass_eq_one` in
`Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`
supply the marked pure-pair atom with `m=1`.  The global reward bound and
positive debt infimum give

\[
 \theta={D_*\over 8R}                               \tag{13.7}
\]

for `|I|=4` in the exact cap case.  With folded debt error at most `D_*/2`,
one may use `theta=D_*/(16R)`.

Thus any proposed Fin4 cap-changing deadline `SD` grammar has an explicit
finite reset count

\[
 K\le\left\lfloor {16RB\over D_*}\right\rfloor
\]

in the exact case (and twice this coarse bound in the approximate case).
The cutoff within each epoch is selected from the actual anchor law, so no
false uniform tightness assumption is made.

This is the strongest finite conclusion probability alone provides.  It does
not manufacture the `Terminal`, `ChargedReturn`, or `StrictRankDrop` branch;
it proves that a complete grammar with those as its only nonneutral branches
must take one at finite depth.  The remaining game-specific obligation is to
define a legal branch at cutoff expiry rather than leaving the execution
undefined.
